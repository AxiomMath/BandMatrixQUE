module

public import BlockBand.Native.ErdosRiabov.Circ.LongSize
public import BlockBand.Native.ErdosRiabov.Circ.ExtraForcing

/-!
# The extra forcing of long chains and the double partial trace

Deterministic bounds on the extra forcing of long regularized chains `k = n+4` and on the partial
trace over two coordinates.

Setting (`d`, `m ≥ 4`, `W ≥ 1`, `P.W = W`, `P.D = d.D`,
`P.S = shortRingProfile d.b m W`, `P.z ∈ 𝒟`), `η_s = vsHeight P.z s`, `L_s = P.lEta s`,
`C_K = vsCK d`, `C₁'' = d.C1pp`, `Ψ^av_{k,s} = P.bigPsiAv k s H`, `β_k = lossBeta k`; sites are
0-based, `k = n+4`.

* **`extraForcing_long`** (long chains, saturated pattern):
  `η_s |F̃_s[𝒳^k_s](x)| ≤ 4 C_K √C₁'' Ψ^av_{k-1,s} L_s^{β_{k-1}} s^av_{k,s}(x)`,
  `F̃ = extraForcingLong` (both pairs), i.e.
  `η|F̃|/(L^{β_k} s^av_k) ≤ 4 C_K √C₁ ψ_{k-1} L^{-(β_k - β_{k-1})}` on `{Ψ^av_{k-1} ≤ ψ_{k-1}}`.
* **`circ_wardTwo`** (Ward identity on two coordinates, for the remainder of the two-ring
  bound): the partial trace over the
  coordinates `x_{k-2}` and `x_k` satisfies
  `|𝒯_{k-2,k}[𝒳^k](x''', x_{k-1})| ≤ η_s⁻² Ψ^av_{k-2,s} L_s^{β_{k-2}} s^av_{k-2,s}(x''', x_{k-1})`,
  constant `1` (only `Split.*` statements and the positivity of `L_s`, `s^av` are used).
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
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate

variable {N : ℕ}

/-!
### Saturation and site bookkeeping
-/

theorem circ_sat_adj {k : ℕ} (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) (i : ℕ)
    (hi : i + 1 < k) : σ ⟨i, by omega⟩ ≠ σ ⟨i + 1, hi⟩ := by
  intro h
  refine hσ ⟨⟨i, by omega⟩, ?_⟩
  unfold patNext
  rw [dite_eq_left hi]
  exact h

theorem circ_removeNth_update_prev {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) :
    Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2))
        (update x ⟨n, by omega⟩ (x ⟨n + 1, by omega⟩)) =
      Fin.removeNth (⟨n, by omega⟩ : Fin (n + 2 + 2)) x := by
  funext i
  rcases lt_trichotomy (i : ℕ) n with h | h | h
  · rw [circ_removeNth_lt _ _ _ (by simp; omega), circ_removeNth_lt _ _ _ (by simp; omega),
      update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  · rw [circ_removeNth_lt _ _ _ (by simp; omega), circ_removeNth_ge _ _ _ (by simp; omega)]
    have e1 : (i.castSucc : Fin (n + 2 + 2)) = ⟨n, by omega⟩ := Fin.ext (by simp; omega)
    have e2 : (i.succ : Fin (n + 2 + 2)) = ⟨n + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1, e2, update_self]
  · rw [circ_removeNth_ge _ _ _ (by simp; omega), circ_removeNth_ge _ _ _ (by simp; omega),
      update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]

theorem circ_wardSites_eq {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) :
    wardSites x = Fin.removeNth (Fin.last (n + 2 + 1)) x := by
  funext i
  rw [circ_removeNth_lt _ _ _ (by simp; omega)]
  rfl

theorem circ_wardSites_update {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) :
    wardSites (update x ⟨n + 2, by omega⟩ (x (Fin.last (n + 2 + 1)))) =
      Fin.removeNth (⟨n + 2, by omega⟩ : Fin (n + 2 + 2)) x := by
  funext i
  simp only [wardSites]
  by_cases h : (i : ℕ) < n + 2
  · rw [circ_removeNth_lt _ _ _ (by simp; omega),
      update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  · rw [circ_removeNth_ge _ _ _ (by simp; omega)]
    have e1 : (i.castSucc : Fin (n + 2 + 2)) = ⟨n + 2, by omega⟩ := Fin.ext (by simp; omega)
    have e2 : (i.succ : Fin (n + 2 + 2)) = Fin.last (n + 2 + 1) := Fin.ext (by simp; omega)
    rw [e1, e2, update_self]

theorem circ_wardSites_update_mid {n : ℕ} (x : Fin (n + 2 + 2) → Fin N) (b : Fin N) :
    wardSites (update x ⟨n + 1, by omega⟩ b) = update (wardSites x) ⟨n + 1, by omega⟩ b := by
  funext i
  simp only [wardSites, update_apply]
  congr 1
  apply propext
  constructor
  · intro e
    exact Fin.ext (by have := congrArg Fin.val e; simpa using this)
  · intro e
    exact Fin.ext (by have := congrArg Fin.val e; simpa using this)

/-!
### One pair
-/

/-- Arithmetic of one pair term: `η ‖T(A + B)‖ ≤ 2 C c Ψ Λ S` from `‖T‖ ≤ C U`,
`‖A‖ ≤ η⁻¹ Ψ Λ s₁`, `‖B‖ ≤ η⁻¹ Ψ Λ s₂` and `U s_i ≤ c S`. -/
theorem circ_pair_bound {T A B : ℂ} {η C U Ψ Λ s₁ s₂ c S : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hΨ : 0 ≤ Ψ) (hΛ : 0 ≤ Λ) (hT : ‖T‖ ≤ C * U) (hA : ‖A‖ ≤ η⁻¹ * (Ψ * (Λ * s₁)))
    (hB : ‖B‖ ≤ η⁻¹ * (Ψ * (Λ * s₂))) (h₁ : U * s₁ ≤ c * S) (h₂ : U * s₂ ≤ c * S) :
    η * ‖T * (A + B)‖ ≤ 2 * C * c * Ψ * Λ * S := by
  rw [norm_mul]
  have hAB := (norm_add_le A B).trans (add_le_add hA hB)
  have h1 : η * (‖T‖ * ‖A + B‖) ≤ η * (C * U * (η⁻¹ * (Ψ * (Λ * s₁)) + η⁻¹ * (Ψ * (Λ * s₂)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hT hAB (norm_nonneg _) (by positivity)) hη.le
  have h2 : η * (C * U * (η⁻¹ * (Ψ * (Λ * s₁)) + η⁻¹ * (Ψ * (Λ * s₂)))) =
      C * Ψ * Λ * (U * s₁ + U * s₂) := by
    field_simp
  have h3 : C * Ψ * Λ * (U * s₁ + U * s₂) ≤ C * Ψ * Λ * (c * S + c * S) :=
    mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
  linarith

/-!
### The extra forcing of long chains
-/

section Long

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W)) (hPW : P.W = W)
  (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
include hm hW hPW hPD hPS hz

/-- **The extra forcing of long chains**, under the hypotheses `Split.CyclicStatement` and
`Split.WardStatement` (`hC`, `hWd`; proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`).
For a saturated pattern `σ` of length `n+4`, `s ∈ [0,1]`, Hermitian `H` and sites `x`:
`η_s |F̃_s[𝒳_s](x)| ≤ 4 C_K √C₁'' Ψ^av_{n+3,s}(H) L_s^{β_{n+3}} s^av_{n+4,s}(x)`,
`F̃ = extraForcingLong`.
-/
theorem extraForcing_long (hC : Split.CyclicStatement) (hWd : Split.WardStatement) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian)
    (x : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s * ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      4 * vsCK d * Real.sqrt d.C1pp * P.bigPsiAv (n + 3) s H * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv x s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := contrVSInputs_of d hm hW P hPW hPD hz hs.1 hs.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hPsi := P.bigPsiAv_nonneg (k := n + 3) s H
  have hΛ : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 3) := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  have hsa : ∀ y : Fin (n + 3) → Fin (m * W), 0 < P.sAv y s := fun y =>
    P.sAv_pos hN hPW' hzi hs.2 y
  -- the kernel bound `|T̂_s| ≤ C_K Υ_s`
  have hK : ∀ a b, ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s a b‖ ≤
      vsCK d * P.ups s a b := by
    intro a b
    have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
      d.D_ge_six hm hW hz hs.1 hs.2).1 a b
    rw [hPS]
    simpa only [PsiData.ups, hPW, hPD, vsCK] using h
  -- the interior partial trace (Ward at the slot `x_{k-2}`)
  have hσm : σ (⟨n + 1, by omega⟩ : Fin (n + 3)).castSucc ≠
      σ (⟨n + 1, by omega⟩ : Fin (n + 3)).succ := circ_sat_adj σ hσ (n + 1) (by omega)
  have hTm : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      ‖∑ b, P.avErr σ (update y ⟨n + 1, by omega⟩ b) s H‖ ≤ (vsHeight P.z s)⁻¹ *
        (P.bigPsiAv (n + 3) s H * (P.lEta s ^ Expo.lossBeta (n + 3) *
          P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) y) s)) := by
    intro y
    have h := circ_wardMid_norm hWd P hS hzi σ ⟨n + 1, by omega⟩ hσm y hs hH
    rw [show ((⟨n + 1, by omega⟩ : Fin (n + 3)).castSucc : Fin (n + 2 + 2)) =
      ⟨n + 1, by omega⟩ from rfl] at h
    refine h.trans ((mul_le_mul_of_nonneg_left (add_le_add
      (circ_norm_avErr_le P _ _ H hL (hsa _)) (circ_norm_avErr_le P _ _ H hL (hsa _)))
      (by positivity)).trans (le_of_eq ?_))
    field_simp
    ring
  -- the closing partial trace
  have hσl : σ (Fin.last (n + 2 + 1)) ≠ σ 0 := circ_last_ne_zero σ hσ
  have hTl : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      ‖∑ b, P.avErr σ (update y (Fin.last (n + 2 + 1)) b) s H‖ ≤ (vsHeight P.z s)⁻¹ *
        (P.bigPsiAv (n + 3) s H * (P.lEta s ^ Expo.lossBeta (n + 3) *
          P.sAv (wardSites y) s)) :=
    fun y => circ_traceLast_le hC hWd P hS hzi σ hσl y hs hH hL (hsa _)
  -- link restorations by the triangle bound for `Υ`
  have hS1 : P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) *
      P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) x) s ≤
        Real.sqrt d.C1pp * P.sAv x s :=
    circ_sAv_removeNth_le (m := n + 1) P hin x ⟨n + 1, by omega⟩ (Or.inl (by
      congr 1
      apply Fin.ext
      simp only
      rw [show n + 1 + (n + 1 + 2) = n + (n + 1 + 3) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]))
  have hS2 : P.ups s (x ⟨n, by omega⟩) (x ⟨n + 1, by omega⟩) *
      P.sAv (Fin.removeNth (⟨n, by omega⟩ : Fin (n + 2 + 2)) x) s ≤
        Real.sqrt d.C1pp * P.sAv x s := by
    rw [hin.symm]
    exact circ_sAv_removeNth_le (m := n + 1) P hin x ⟨n, by omega⟩ (Or.inr (by
      congr 1
      apply Fin.ext
      simp only
      rw [Nat.mod_eq_of_lt (by omega)]))
  have hS3 : P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
      P.sAv (wardSites x) s ≤ Real.sqrt d.C1pp * P.sAv x s := by
    rw [circ_wardSites_eq]
    exact circ_sAv_removeNth_le (m := n + 1) P hin x (Fin.last (n + 2 + 1)) (Or.inl (by
      congr 1
      apply Fin.ext
      simp only [Fin.val_last]
      rw [show n + 2 + 1 + (n + 1 + 2) = n + 2 + (n + 1 + 3) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]))
  have hS4 : P.ups s (x ⟨n + 2, by omega⟩) (x (Fin.last (n + 2 + 1))) *
      P.sAv (wardSites (update x ⟨n + 2, by omega⟩ (x (Fin.last (n + 2 + 1))))) s ≤
        Real.sqrt d.C1pp * P.sAv x s := by
    rw [circ_wardSites_update, hin.symm]
    have hl : x (Fin.last (n + 2 + 1)) = x ⟨n + 3, by omega⟩ := rfl
    rw [hl]
    exact circ_sAv_removeNth_le (m := n + 1) P hin x ⟨n + 2, by omega⟩ (Or.inr (by
      congr 1
      apply Fin.ext
      simp only
      rw [Nat.mod_eq_of_lt (by omega)]))
  -- assembly
  have hE : extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x =
      vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x ⟨n, by omega⟩)
          (x ⟨n + 1, by omega⟩) *
        (∑ b, P.avErr σ (update (update x ⟨n, by omega⟩ (x ⟨n + 1, by omega⟩))
            ⟨n + 1, by omega⟩ b) s H +
          ∑ b, P.avErr σ (update x ⟨n + 1, by omega⟩ b) s H) +
      vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x ⟨n + 2, by omega⟩)
          (x (Fin.last (n + 2 + 1))) *
        (∑ b, P.avErr σ (update (update x ⟨n + 2, by omega⟩ (x (Fin.last (n + 2 + 1))))
            (Fin.last (n + 2 + 1)) b) s H +
          ∑ b, P.avErr σ (update x (Fin.last (n + 2 + 1)) b) s H) := rfl
  have hA1 := hTm (update x ⟨n, by omega⟩ (x ⟨n + 1, by omega⟩))
  rw [circ_removeNth_update_prev] at hA1
  have hP1 := circ_pair_bound hη hCK (hin.nonneg _ _) hPsi hΛ (hK _ _) hA1 (hTm x) hS2 hS1
  have hP2 := circ_pair_bound hη hCK (hin.nonneg _ _) hPsi hΛ (hK _ _)
    (hTl (update x ⟨n + 2, by omega⟩ (x (Fin.last (n + 2 + 1))))) (hTl x) hS4 hS3
  rw [hE]
  calc vsHeight P.z s * ‖_ + _‖ ≤ vsHeight P.z s * ‖_‖ + vsHeight P.z s * ‖_‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hη.le
    _ ≤ _ := by linarith

end Long

/-!
### The partial trace over two coordinates
-/

/-- Under the hypotheses `Split.CyclicStatement` and `Split.WardStatement` (proved as
`MTerms.cyclic_holds`, `MTerms.ward_holds`): for stochastic symmetric `S`, `N, W ≥ 1`,
`Im z > 0`, a saturated pattern of length `k = n+4`, `s ∈ [0,1]` and Hermitian `H`:
`|Σ_{b,c} 𝒳^k(x[x_{k-2} ↦ b][x_k ↦ c])| ≤ η_s⁻² Ψ^av_{k-2,s} L_s^{β_{k-2}} s^av_{k-2,s}(y)`,
`y = (x_1, …, x_{k-3}, x_{k-1})` (`x` without `x_{k-2}`, `x_k`).
-/
theorem circ_wardTwo (hC : Split.CyclicStatement) (hWd : Split.WardStatement) (P : PsiData N)
    (hS : StochasticSymm P.S) (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (x : Fin (n + 2 + 2) → Fin N) :
    ‖∑ b, ∑ c, P.avErr σ (update (update x ⟨n + 1, by omega⟩ b) (Fin.last (n + 2 + 1)) c) s H‖ ≤
      (vsHeight P.z s)⁻¹ ^ 2 * (P.bigPsiAv (n + 2) s H * (P.lEta s ^ Expo.lossBeta (n + 2) *
        P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) (wardSites x)) s)) := by
  have hη := vsHeight_pos hz hs.2
  have hL := P.lEta_pos hN hW hz hs.2
  have hσl : σ (Fin.last (n + 2 + 1)) ≠ σ 0 := circ_last_ne_zero σ hσ
  set y := Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) (wardSites x)
  set B := P.bigPsiAv (n + 2) s H * (P.lEta s ^ Expo.lossBeta (n + 2) * P.sAv y s) with hB
  have hsa := P.sAv_pos hN hW hz hs.2 y
  have hB0 : 0 ≤ B := by
    have := P.bigPsiAv_nonneg (k := n + 2) s H
    have := Real.rpow_nonneg hL.le (Expo.lossBeta (n + 2))
    positivity
  -- the closing pair, then the interior pair on the two `(k-1)`-chains
  have hinner : ∀ b, ∑ c, P.avErr σ (update (update x ⟨n + 1, by omega⟩ b)
      (Fin.last (n + 2 + 1)) c) s H =
      (patZ P.z σ s (Fin.last (n + 2 + 1)) - patZ P.z σ s 0)⁻¹ *
        (P.avErr (wardPatLast σ) (update (wardSites x) ⟨n + 1, by omega⟩ b) s H -
          P.avErr (wardPatHead σ) (update (wardSites x) ⟨n + 1, by omega⟩ b) s H) := by
    intro b
    rw [wardReduction hC hWd P hS hz σ hσl _ hs hH, circ_wardSites_update_mid]
  simp only [hinner]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, norm_mul, norm_inv]
  have h2 := two_eta_le_norm_patZ_sub (z := P.z) σ (t := s) hσl
  have hmid : ∀ τ : Fin (n + 3) → Bool, τ (Fin.last (n + 1)).castSucc ≠ τ (Fin.last (n + 1)).succ →
      ‖∑ b, P.avErr τ (update (wardSites x) ⟨n + 1, by omega⟩ b) s H‖ ≤
        (2 * vsHeight P.z s)⁻¹ * (2 * B) := by
    intro τ hτ
    have h := circ_wardMid_norm hWd P hS hz τ (Fin.last (n + 1)) hτ (wardSites x) hs hH
    rw [show ((Fin.last (n + 1)).castSucc : Fin (n + 3)) = ⟨n + 1, by omega⟩ from rfl] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h1 := circ_norm_avErr_le P (Fin.removeNth (Fin.last (n + 1)).succ τ) y H hL hsa
    have h2 := circ_norm_avErr_le P (Fin.removeNth ⟨n + 1, by omega⟩ τ) y H hL hsa
    linarith
  have hτ1 : wardPatLast σ (Fin.last (n + 1)).castSucc ≠ wardPatLast σ (Fin.last (n + 1)).succ := by
    have e1 : ((Fin.last (n + 1)).castSucc : Fin (n + 3)) ≠ 0 := by
      intro e; have := congrArg Fin.val e; simp at this
    have e2 : ((Fin.last (n + 1)).succ : Fin (n + 3)) ≠ 0 := Fin.succ_ne_zero _
    simp only [wardPatLast, e1, e2, ite_false]
    exact circ_sat_adj σ hσ (n + 1) (by omega)
  have hτ2 : wardPatHead σ (Fin.last (n + 1)).castSucc ≠ wardPatHead σ (Fin.last (n + 1)).succ :=
    circ_sat_adj σ hσ (n + 1) (by omega)
  have hm1 := hmid _ hτ1
  have hm2 := hmid _ hτ2
  have hsub := (norm_sub_le _ _).trans (add_le_add hm1 hm2)
  calc ‖patZ P.z σ s (Fin.last (n + 2 + 1)) - patZ P.z σ s 0‖⁻¹ * ‖_ - _‖
      ≤ (2 * vsHeight P.z s)⁻¹ * ((2 * vsHeight P.z s)⁻¹ * (2 * B) +
          (2 * vsHeight P.z s)⁻¹ * (2 * B)) :=
        mul_le_mul ((inv_le_inv₀ (by linarith) (by positivity)).mpr h2) hsub (norm_nonneg _)
          (by positivity)
    _ = _ := by field_simp; ring

end BlockBand.Native.ErdosRiabov.Circ
