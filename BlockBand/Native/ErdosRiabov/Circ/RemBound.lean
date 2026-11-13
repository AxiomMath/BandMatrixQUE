module

public import BlockBand.Native.ErdosRiabov.Circ.RemDecomp
public import BlockBand.Native.ErdosRiabov.Circ.BoundLin

/-!
# The remainder of the long linear term

Deterministic bounds on the three remainders `𝓡ᵢ` of the long linear term, giving the
regularized-to-linear input (LL) of `linTerm_long`.

Setting (`d`, `m ≥ 4`, `W ≥ 1`, `P.W = W`, `P.D = d.D`,
`P.S = shortRingProfile d.b m W`, `P.z ∈ 𝒟`), a saturated pattern of length `k = n+4 ≤ 8`, and the
a priori hypothesis `Forcing.APriori P s H ψ^I ψ^A` (`Ψ_{j,s} ≤ ψ_j`, given for `s ≤ τ` by
`Apriori.forcingAPriori_of_le_tau`). `η = η_s`, `L = L_s`, `C_K = vsCK d`, `C_w = d.Cwc`,
`C₁ = d.C1pp`, `𝒳 = 𝒳^k_s`, `𝓡ᵢ` the remainders `circRemOne`, `circRemTwo`, `circRemThree` with
`T̂_s`.
The Schwarz bound for `Υ` is called (U6) and the triangle bound (U4).

* `circ_C10_mid`: (U6) at the interior coordinate `x_{k-2}` of a `(k-1)`-chain:
  `Σ_c |K(w_{k-2}, c)| s^av(w[k-2 ↦ c]) ≤ C_K (C_w/η) s^av(w)` for `|K| ≤ C_K Υ`.
* **`circ_remOne_bound`**, **`circ_remTwo_bound`**:
  `η² |𝓡ᵢ(x)| ≤ C_K² C_w √C₁ ψ_{k-1} L^{β_{k-1}} s^av_k(x)`
  (the Ward identity resp. `circ_traceMid_le`, (U6), (U4)).
* **`circ_remThree_bound`**: `η² |𝓡₃(x)| ≤ C_K² C₁ ψ_{k-2} L^{β_{k-2}} s^av_k(x)` (`circ_wardTwo`,
  (U4) twice).
* **`circ_LL_bound`** (the (LL) hypothesis of `linTerm_long`, at one time `s`): if `L ≥ 1` and
  `η² |Θ̊^{(k-2)} Θ̊^{(k)}[𝒳](y)| ≤ B_Z L^{β_k} s^av_k(y)` (the two-ring bound at time `s`), then
  `η² |T̂^{(k-2)} T̂^{(k)}[𝒳](y)| ≤`
  `(B_Z + 2 C_K² C_w √C₁ ψ_{k-1} + C_K² C₁ ψ_{k-2}) L^{β_k} s^av_k(y)`.
  Normalized: `η²|𝓡|/(L^{β_k} s^av_k) ≤ 2C_K²C_w√C₁ ψ_{k-1} L^{-(β_k-β_{k-1})} +
  C_K²C₁ ψ_{k-2} L^{-(β_k-β_{k-2})}` (the three bounds above).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate

variable {N : ℕ}

/-!
### Site bookkeeping
-/

theorem circ_trace_slot_mid {n : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (f : CircFun N (n + 2 + 2))
    (x : Fin (n + 2 + 2) → Fin N) :
    ∑ b, circSlot ⟨n + 1, by omega⟩ K f (update x (Fin.last (n + 2 + 1)) b) =
      ∑ c, K (x ⟨n + 1, by omega⟩) c *
        ∑ b, f (update (update x ⟨n + 1, by omega⟩ c) (Fin.last (n + 2 + 1)) b) := by
  have hl : (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) ≠ Fin.last (n + 2 + 1) := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
  simp only [circSlot_apply, update_of_ne hl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [update_comm hl]

theorem circ_trace_slot_last {n : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (f : CircFun N (n + 2 + 2))
    (x : Fin (n + 2 + 2) → Fin N) :
    ∑ b, circSlot (Fin.last (n + 2 + 1)) K f (update x ⟨n + 1, by omega⟩ b) =
      ∑ c, K (x (Fin.last (n + 2 + 1))) c *
        ∑ b, f (update (update x (Fin.last (n + 2 + 1)) c) ⟨n + 1, by omega⟩ b) := by
  have hl : (Fin.last (n + 2 + 1) : Fin (n + 2 + 2)) ≠ ⟨n + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
  simp only [circSlot_apply, update_of_ne hl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [update_comm hl]

theorem circ_removeNth_update_last {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) (c : Fin N) :
    Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) (update x (Fin.last (n + 2 + 1)) c) =
      update (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) x) (Fin.last (n + 2)) c := by
  funext i
  by_cases hl : i = Fin.last (n + 2)
  · subst hl
    rw [update_self, circ_removeNth_ge _ _ _ (by simp)]
    exact update_self _ _ _
  · rw [update_of_ne hl]
    have hl' : (i : ℕ) ≠ n + 2 := fun e => hl (Fin.ext (by simpa using e))
    by_cases h : (i : ℕ) < n + 1
    · rw [circ_removeNth_lt _ _ _ (by simpa using h), circ_removeNth_lt _ _ _ (by simpa using h),
        update_of_ne (by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]; omega)]
    · rw [circ_removeNth_ge _ _ _ (by simp only; omega),
        circ_removeNth_ge _ _ _ (by simp only; omega),
        update_of_ne (by simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_last]; omega)]

theorem circ_removeNth_last_val {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) :
    Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) x (Fin.last (n + 2)) =
      x (Fin.last (n + 2 + 1)) := by
  rw [circ_removeNth_ge _ _ _ (by simp)]
  rfl

/-!
### The Schwarz bound at the interior coordinate
-/

theorem circ_cyc_mid (U : Matrix (Fin N) (Fin N) ℝ) {n : ℕ} (y : Fin (n + 3) → Fin N) :
    ∏ e : Fin (n + 3), U (y e) (y (finRotate (n + 3) e)) =
      (∏ e : Fin n, U (y e.castSucc.castSucc.castSucc) (y e.castSucc.castSucc.succ)) *
        U (y ⟨n, by omega⟩) (y ⟨n + 1, by omega⟩) * U (y ⟨n + 1, by omega⟩) (y (Fin.last (n + 2))) *
          U (y (Fin.last (n + 2))) (y 0) := by
  rw [circ_cyc_eq, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  rfl

/-- **(U6) at the interior coordinate `k-2` of a `(k-1)`-chain** (the `𝓡₁` step):
for `w : Fin (n+3) → Fin N` and `|K| ≤ C_K Υ_t`:
`Σ_c |K(w_{n+1}, c)| s^av_t(w[n+1 ↦ c]) ≤ C_K (C_w/η_t) s^av_t(w)`. -/
theorem circ_C10_mid (d : VSData) {P : PsiData N} {t : ℝ} (hin : QV.QVInputs d P t)
    (K : Matrix (Fin N) (Fin N) ℂ) {CK : ℝ} (hCK : 0 ≤ CK)
    (hK : ∀ x y, ‖K x y‖ ≤ CK * P.ups t x y) {n : ℕ} (w : Fin (n + 3) → Fin N) :
    ∑ c, ‖K (w ⟨n + 1, by omega⟩) c‖ * P.sAv (update w ⟨n + 1, by omega⟩ c) t ≤
      CK * (d.Cwc / vsHeight P.z t) * P.sAv w t := by
  set U := P.ups t
  set i : Fin (n + 3) := ⟨n + 1, by omega⟩
  have hn0 : (⟨n, by omega⟩ : Fin (n + 3)) ≠ i := by
    simp only [ne_eq, Fin.ext_iff, i]; omega
  have hnl : (Fin.last (n + 2) : Fin (n + 3)) ≠ i := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last, i]; omega
  have hn00 : (0 : Fin (n + 3)) ≠ i := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, i]; omega
  set Q0 := ∏ e : Fin n, U (w e.castSucc.castSucc.castSucc) (w e.castSucc.castSucc.succ) with hQ0
  have hQ0c : ∀ c, ∏ e : Fin n, U (update w i c e.castSucc.castSucc.castSucc)
      (update w i c e.castSucc.castSucc.succ) = Q0 := by
    intro c
    refine Finset.prod_congr rfl fun e _ => ?_
    have he := e.isLt
    rw [update_of_ne (by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, i]; omega),
      update_of_ne (by simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i]; omega)]
  set Q := Q0 * U (w (Fin.last (n + 2))) (w 0) with hQ
  have hQn : 0 ≤ Q := mul_nonneg (Finset.prod_nonneg fun e _ => hin.nonneg _ _) (hin.nonneg _ _)
  have hsa : ∀ y : Fin (n + 3) → Fin N, P.sAv y t = P.lEta t ^ (-((n + 3 : ℕ) : ℝ) / 2) *
      Real.sqrt (∏ e : Fin (n + 3), U (y e) (y (finRotate (n + 3) e))) := by
    intro y
    unfold PsiData.sAv
    rw [ite_eq_right (by omega)]
  have hcw : ∏ e : Fin (n + 3), U (w e) (w (finRotate (n + 3) e)) =
      Q * (U (w i) (w (Fin.last (n + 2))) * U (w ⟨n, by omega⟩) (w i)) := by
    rw [circ_cyc_mid]
    simp only [hQ, ← hQ0]
    ring
  have hcc : ∀ c, ∏ e : Fin (n + 3), U (update w i c e) (update w i c (finRotate (n + 3) e)) =
      Q * (U c (w (Fin.last (n + 2))) * U (w ⟨n, by omega⟩) c) := by
    intro c
    rw [circ_cyc_mid, hQ0c, update_of_ne hn0, update_self, update_of_ne hnl, update_of_ne hn00]
    simp only [hQ]
    ring
  have hcore := QV.qv_C10_core d hin K hCK hK hQn (w i) (w (Fin.last (n + 2))) (w ⟨n, by omega⟩)
  have hLp : 0 ≤ P.lEta t ^ (-((n + 3 : ℕ) : ℝ) / 2) := Real.rpow_nonneg hin.lEta_pos.le _
  simp only [hsa, hcc, hcw]
  calc ∑ c, ‖K (w i) c‖ * (P.lEta t ^ (-((n + 3 : ℕ) : ℝ) / 2) *
        Real.sqrt (Q * (U c (w (Fin.last (n + 2))) * U (w ⟨n, by omega⟩) c)))
      = P.lEta t ^ (-((n + 3 : ℕ) : ℝ) / 2) * ∑ c, ‖K (w i) c‖ *
          Real.sqrt (Q * (U c (w (Fin.last (n + 2))) * U (w ⟨n, by omega⟩) c)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ ≤ P.lEta t ^ (-((n + 3 : ℕ) : ℝ) / 2) * (CK * (d.Cwc / vsHeight P.z t) *
          Real.sqrt (Q * (U (w i) (w (Fin.last (n + 2))) * U (w ⟨n, by omega⟩) (w i)))) :=
        mul_le_mul_of_nonneg_left hcore hLp
    _ = _ := by ring

theorem circ_lossBeta_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 8) :
    Expo.lossBeta j ≤ Expo.lossBeta k := by
  rcases Nat.eq_or_lt_of_le hjk with h | h
  · rw [h]
  rw [Forcing.lossBeta_eq (by omega)]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [Forcing.lossBeta_eq (by omega)]
    exact Forcing.lossAlpha_mono (by omega)
  · rw [show k = 8 by omega, Forcing.lossBeta_eight]
    have := Forcing.lossAlpha_mono (show j + 1 ≤ 8 by omega)
    rw [Forcing.lossAlpha_eight] at this
    linarith

/-!
### The three remainders
-/

section Rem

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W)) (hPW : P.W = W)
  (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
include hm hW hPW hPD hPS hz

theorem circ_rem_kernel {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (a b : Fin (m * W)) :
    ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s a b‖ ≤ vsCK d * P.ups s a b := by
  have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
    d.D_ge_six hm hW hz hs.1 hs.2).1 a b
  rw [hPS]
  simpa only [PsiData.ups, hPW, hPD, vsCK] using h

/-- **The remainder of the long linear term, `𝓡₁`**: for a saturated pattern of length
`k = n+4 ≤ 8` and `Forcing.APriori` at time `s`:
`η² |𝓡₁(x)| ≤ C_K² C_w √C₁ ψ_{k-1} L^{β_{k-1}} s^av_k(x)`.
-/
theorem circ_remOne_bound {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ}
    (hAP : Forcing.APriori P s H psiI psiA) (x : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 * ‖circRemOne P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv x s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := QV.qvInputs_of d hm hW P hPW hPD hPS hz hs.1 hs.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hΨ : P.bigPsiAv (n + 3) s H ≤ psiA (n + 3) :=
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hP0 := P.bigPsiAv_nonneg (k := n + 3) s H
  have hLb : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 3) := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  have hσl : σ (Fin.last (n + 2 + 1)) ≠ σ 0 := circ_last_ne_zero σ hσ
  set w := wardSites x with hw
  -- the Ward identity at every `c`
  have hT : ∀ c, ‖∑ b, P.avErr σ (update (update x ⟨n + 1, by omega⟩ c) (Fin.last (n + 2 + 1)) b)
      s H‖ ≤ (vsHeight P.z s)⁻¹ * (psiA (n + 3) * (P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv (update w ⟨n + 1, by omega⟩ c) s)) := by
    intro c
    have h := Discharge.circ_traceLast_le_uncond P hS hzi σ hσl (update x ⟨n + 1, by omega⟩ c) hs
      hH hL (P.sAv_pos hN hPW' hzi hs.2 _)
    rw [circ_wardSites_update_mid] at h
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΨ
      (mul_nonneg hLb (P.sAv_pos hN hPW' hzi hs.2 _).le)) (inv_nonneg.mpr hη.le))
  -- (U6)
  have hC10 := circ_C10_mid d hin _ hCK (circ_rem_kernel d hm hW P hPW hPD hPS hz hs) w
  have hwi : w ⟨n + 1, by omega⟩ = x ⟨n + 1, by omega⟩ := rfl
  rw [hwi] at hC10
  -- (U4)
  have hU4 : P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) * P.sAv w s ≤
      Real.sqrt d.C1pp * P.sAv x s := by
    rw [hw, circ_wardSites_eq]
    exact circ_sAv_removeNth_le (m := n + 1) P hin.toContrVSInputs x (Fin.last (n + 2 + 1))
      (Or.inl (by
        congr 1
        apply Fin.ext
        simp only [Fin.val_last]
        rw [show n + 2 + 1 + (n + 1 + 2) = n + 2 + (n + 1 + 3) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]))
  have hsum : ‖∑ c, vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
      (x ⟨n + 1, by omega⟩) c * ∑ b, P.avErr σ (update (update x ⟨n + 1, by omega⟩ c)
        (Fin.last (n + 2 + 1)) b) s H‖ ≤
      (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
        (vsCK d * (d.Cwc / vsHeight P.z s) * P.sAv w s) := by
    refine (norm_sum_le _ _).trans ?_
    have hc0 : 0 ≤ (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) :=
      mul_nonneg (inv_nonneg.mpr hη.le) (mul_nonneg (hP0.trans hΨ) hLb)
    calc ∑ c, ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
          (x ⟨n + 1, by omega⟩) c * ∑ b, P.avErr σ (update (update x ⟨n + 1, by omega⟩ c)
            (Fin.last (n + 2 + 1)) b) s H‖
        ≤ ∑ c, (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
            (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
              (x ⟨n + 1, by omega⟩) c‖ * P.sAv (update w ⟨n + 1, by omega⟩ c) s) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul]
          refine (mul_le_mul_of_nonneg_left (hT c) (norm_nonneg _)).trans (le_of_eq ?_)
          ring
      _ = _ := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hC10 hc0
  have hK := circ_rem_kernel d hm hW P hPW hPD hPS hz hs (x ⟨n + 2, by omega⟩)
    (x (Fin.last (n + 2 + 1)))
  have hU := hin.nonneg (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1)))
  have hsw := (P.sAv_pos hN hPW' hzi hs.2 w).le
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  unfold circRemOne
  rw [circ_trace_slot_mid, norm_mul]
  calc vsHeight P.z s ^ 2 * (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
        (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1)))‖ * ‖_‖)
      ≤ vsHeight P.z s ^ 2 * (vsCK d * P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
          ((vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
            (vsCK d * (d.Cwc / vsHeight P.z s) * P.sAv w s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hK hsum (norm_nonneg _) (by positivity))
          (by positivity)
    _ = vsCK d ^ 2 * d.Cwc * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
          (P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) * P.sAv w s) := by
        field_simp
    _ ≤ vsCK d ^ 2 * d.Cwc * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
          (Real.sqrt d.C1pp * P.sAv x s) :=
        mul_le_mul_of_nonneg_left hU4 (by have := hP0.trans hΨ; positivity)
    _ = _ := by ring

/-- **The remainder of the long linear term, `𝓡₂`**: under the hypotheses of
`circ_remOne_bound`:
`η² |𝓡₂(x)| ≤ C_K² C_w √C₁ ψ_{k-1} L^{β_{k-1}} s^av_k(x)`.
-/
theorem circ_remTwo_bound {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ}
    (hAP : Forcing.APriori P s H psiI psiA) (x : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 * ‖circRemTwo P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv x s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := QV.qvInputs_of d hm hW P hPW hPD hPS hz hs.1 hs.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hΨ : P.bigPsiAv (n + 3) s H ≤ psiA (n + 3) :=
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hP0 := P.bigPsiAv_nonneg (k := n + 3) s H
  have hLb : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 3) := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  have hσm : σ ⟨n + 1, by omega⟩ ≠ σ ⟨n + 2, by omega⟩ := circ_sat_adj σ hσ (n + 1) (by omega)
  set v := Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) x with hv
  -- the interior Ward identity at every `c`
  have hT : ∀ c, ‖∑ b, P.avErr σ (update (update x (Fin.last (n + 2 + 1)) c) ⟨n + 1, by omega⟩ b)
      s H‖ ≤ (vsHeight P.z s)⁻¹ * (psiA (n + 3) * (P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv (update v (Fin.last (n + 2)) c) s)) := by
    intro c
    have h := circ_traceMid_le P hS hzi σ hσm (update x (Fin.last (n + 2 + 1)) c) hs hH hL
      (P.sAv_pos hN hPW' hzi hs.2 _)
    rw [circ_removeNth_update_last] at h
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΨ
      (mul_nonneg hLb (P.sAv_pos hN hPW' hzi hs.2 _).le)) (inv_nonneg.mpr hη.le))
  
  have hC10 : ∑ c, ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
      (v (Fin.last (n + 2))) c‖ * P.sAv (update v (Fin.last (n + 2)) c) s ≤
        vsCK d * (d.Cwc / vsHeight P.z s) * P.sAv v s :=
    QV.qv_thetaSAv d hin _ hCK (circ_rem_kernel d hm hW P hPW hPD hPS hz hs) (n := n + 1) v
  rw [hv, circ_removeNth_last_val, ← hv] at hC10
  -- (U4)
  have hU4 : P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) * P.sAv v s ≤
      Real.sqrt d.C1pp * P.sAv x s :=
    circ_sAv_removeNth_le (m := n + 1) P hin.toContrVSInputs x ⟨n + 1, by omega⟩ (Or.inl (by
      congr 1
      apply Fin.ext
      simp only
      rw [show n + 1 + (n + 1 + 2) = n + (n + 1 + 3) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]))
  have hsum : ‖∑ c, vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
      (x (Fin.last (n + 2 + 1))) c * ∑ b, P.avErr σ (update (update x (Fin.last (n + 2 + 1)) c)
        ⟨n + 1, by omega⟩ b) s H‖ ≤
      (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
        (vsCK d * (d.Cwc / vsHeight P.z s) * P.sAv v s) := by
    refine (norm_sum_le _ _).trans ?_
    have hc0 : 0 ≤ (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) :=
      mul_nonneg (inv_nonneg.mpr hη.le) (mul_nonneg (hP0.trans hΨ) hLb)
    calc ∑ c, ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
          (x (Fin.last (n + 2 + 1))) c * ∑ b, P.avErr σ (update (update x (Fin.last (n + 2 + 1)) c)
            ⟨n + 1, by omega⟩ b) s H‖
        ≤ ∑ c, (vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
            (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
              (x (Fin.last (n + 2 + 1))) c‖ * P.sAv (update v (Fin.last (n + 2)) c) s) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul]
          refine (mul_le_mul_of_nonneg_left (hT c) (norm_nonneg _)).trans (le_of_eq ?_)
          ring
      _ = _ := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hC10 hc0
  have hK := circ_rem_kernel d hm hW P hPW hPD hPS hz hs (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩)
  rw [hin.symm] at hK
  have hU := hin.nonneg (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩)
  have hsv := (P.sAv_pos hN hPW' hzi hs.2 v).le
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  unfold circRemTwo
  rw [circ_trace_slot_last, norm_mul]
  calc vsHeight P.z s ^ 2 * (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
        (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩)‖ * ‖_‖)
      ≤ vsHeight P.z s ^ 2 * (vsCK d * P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) *
          ((vsHeight P.z s)⁻¹ * (psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3)) *
            (vsCK d * (d.Cwc / vsHeight P.z s) * P.sAv v s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hK hsum (norm_nonneg _) (by positivity))
          (by positivity)
    _ = vsCK d ^ 2 * d.Cwc * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
          (P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) * P.sAv v s) := by
        field_simp
    _ ≤ vsCK d ^ 2 * d.Cwc * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
          (Real.sqrt d.C1pp * P.sAv x s) :=
        mul_le_mul_of_nonneg_left hU4 (by have := hP0.trans hΨ; positivity)
    _ = _ := by ring

/-- **The remainder of the long linear term, `𝓡₃`**: under the hypotheses of
`circ_remOne_bound`:
`η² |𝓡₃(x)| ≤ C_K² C₁ ψ_{k-2} L^{β_{k-2}} s^av_k(x)` (`circ_wardTwo` and (U4) twice).
-/
theorem circ_remThree_bound {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ}
    (hAP : Forcing.APriori P s H psiI psiA) (x : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 * ‖circRemThree P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      vsCK d ^ 2 * d.C1pp * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) * P.sAv x s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := QV.qvInputs_of d hm hW P hPW hPD hPS hz hs.1 hs.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hΨ : P.bigPsiAv (n + 2) s H ≤ psiA (n + 2) :=
    (hAP (n + 2) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hP0 := P.bigPsiAv_nonneg (k := n + 2) s H
  have hLb : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 2) := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  set w := wardSites x with hw
  set y := Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) w with hy
  have hW2 := Discharge.circ_wardTwo_uncond P hS hN hPW' hzi σ hσ hs hH x
  rw [← hw, ← hy] at hW2
  have hU4a : P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) * P.sAv w s ≤
      Real.sqrt d.C1pp * P.sAv x s := by
    rw [hw, circ_wardSites_eq]
    exact circ_sAv_removeNth_le (m := n + 1) P hin.toContrVSInputs x (Fin.last (n + 2 + 1))
      (Or.inl (by
        congr 1
        apply Fin.ext
        simp only [Fin.val_last]
        rw [show n + 2 + 1 + (n + 1 + 2) = n + 2 + (n + 1 + 3) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]))
  have hU4b : P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) * P.sAv y s ≤
      Real.sqrt d.C1pp * P.sAv w s :=
    circ_sAv_removeNth_le (m := n) P hin.toContrVSInputs w ⟨n + 1, by omega⟩ (Or.inl (by
      congr 1
      apply Fin.ext
      show n = (n + 1 + (n + 2)) % (n + 3)
      rw [show n + 1 + (n + 2) = n + (n + 3) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]))
  have hK1 := circ_rem_kernel d hm hW P hPW hPD hPS hz hs (x ⟨n + 2, by omega⟩)
    (x (Fin.last (n + 2 + 1)))
  have hK2 := circ_rem_kernel d hm hW P hPW hPD hPS hz hs (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩)
  rw [hin.symm (x ⟨n + 1, by omega⟩)] at hK2
  have hU1 := hin.nonneg (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1)))
  have hU2 := hin.nonneg (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩)
  have hsy := (P.sAv_pos hN hPW' hzi hs.2 y).le
  have hsw := (P.sAv_pos hN hPW' hzi hs.2 w).le
  have hC := Real.sqrt_nonneg d.C1pp
  have hCC : Real.sqrt d.C1pp * Real.sqrt d.C1pp = d.C1pp :=
    Real.mul_self_sqrt (le_trans zero_le_one d.one_le_C1pp)
  have hψ := hP0.trans hΨ
  unfold circRemThree
  rw [norm_mul, norm_mul]
  calc vsHeight P.z s ^ 2 * (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
        (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1)))‖ *
        ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x ⟨n + 1, by omega⟩)
          (x ⟨n, by omega⟩)‖ * ‖_‖)
      ≤ vsHeight P.z s ^ 2 * (vsCK d * P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
          (vsCK d * P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩)) *
            ((vsHeight P.z s)⁻¹ ^ 2 * (psiA (n + 2) * (P.lEta s ^ Expo.lossBeta (n + 2) *
              P.sAv y s)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hK1 hK2 (norm_nonneg _)
          (by positivity)) (hW2.trans ?_) (norm_nonneg _) (by positivity)) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΨ (mul_nonneg hLb hsy))
          (by positivity)
    _ = vsCK d ^ 2 * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) *
          (P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
            (P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) * P.sAv y s)) := by
        field_simp
    _ ≤ vsCK d ^ 2 * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) *
          (P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
            (Real.sqrt d.C1pp * P.sAv w s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU4b hU1) (by positivity)
    _ = vsCK d ^ 2 * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) * Real.sqrt d.C1pp *
          (P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) * P.sAv w s) := by ring
    _ ≤ vsCK d ^ 2 * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) * Real.sqrt d.C1pp *
          (Real.sqrt d.C1pp * P.sAv x s) :=
        mul_le_mul_of_nonneg_left hU4a (by positivity)
    _ = _ := by
        linear_combination (vsCK d ^ 2 * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) *
          P.sAv x s) * hCC

/-- Under the hypotheses of `circ_remOne_bound`, `1 ≤ L_s` and the two-ring bound
`η² |Θ̊^{(k-2)} Θ̊^{(k)}[𝒳](y)| ≤ B_Z L^{β_k} s^av_k(y)` for all `y`:
`η² |T̂^{(k-2)} T̂^{(k)}[𝒳](y)| ≤`
`(B_Z + 2 C_K² C_w √C₁ ψ_{k-1} + C_K² C₁ ψ_{k-2}) L^{β_k} s^av_k(y)`.
-/
theorem circ_LL_bound {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ}
    (hAP : Forcing.APriori P s H psiI psiA) (hL1 : 1 ≤ P.lEta s) {BZ : ℝ}
    (hZ : ∀ y, vsHeight P.z s ^ 2 * ‖ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
      (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
        (fun y => P.avErr σ y s H)) y‖ ≤ BZ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (y : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s H)) y‖ ≤
      (BZ + 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) +
        vsCK d ^ 2 * d.C1pp * psiA (n + 2)) * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hdec := congrFun (circ_twoSlot_decomp hS hzi.ne' hs (fun y => P.avErr σ y s H)) y
  simp only [Pi.add_apply, Pi.sub_apply] at hdec
  rw [hdec]
  have h1 := circ_remOne_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h2 := circ_remTwo_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h3 := circ_remThree_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h0 := hZ y
  have hL3 : P.lEta s ^ Expo.lossBeta (n + 3) ≤ P.lEta s ^ Expo.lossBeta (n + 4) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (circ_lossBeta_mono (by omega) hn)
  have hL2 : P.lEta s ^ Expo.lossBeta (n + 2) ≤ P.lEta s ^ Expo.lossBeta (n + 4) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (circ_lossBeta_mono (by omega) hn)
  have hsy := (P.sAv_pos hN hPW' hzi hs.2 y).le
  have hψ3 : 0 ≤ psiA (n + 3) := (P.bigPsiAv_nonneg (k := n + 3) s H).trans
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hψ2 : 0 ≤ psiA (n + 2) := (P.bigPsiAv_nonneg (k := n + 2) s H).trans
    (hAP (n + 2) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hc1 : 0 ≤ vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) := by
    have := le_trans zero_le_one d.one_le_Cwc
    positivity
  have hc2 : 0 ≤ vsCK d ^ 2 * d.C1pp * psiA (n + 2) := by
    have := le_trans zero_le_one d.one_le_C1pp
    positivity
  have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL3 hc1) hsy
  have e2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 hc2) hsy
  set A := ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
    (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ (fun y => P.avErr σ y s H)) y
  set B := circRemOne P.S P.z s (fun y => P.avErr σ y s H) y
  set C := circRemTwo P.S P.z s (fun y => P.avErr σ y s H) y
  set D := circRemThree P.S P.z s (fun y => P.avErr σ y s H) y
  have htri : ‖A + B + C - D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    have a1 := norm_sub_le (A + B + C) D
    have a2 := norm_add_le (A + B) C
    have a3 := norm_add_le A B
    linarith
  have hη2 : 0 ≤ vsHeight P.z s ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left htri hη2
  nlinarith [this, h0, h1, h2, h3, e1, e2]

end Rem

end BlockBand.Native.ErdosRiabov.Circ
