module

public import BlockBand.Native.ErdosRiabov.MBound.Ops
public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit

/-!
# Three local facts on `s^av`

Kernel actions, site removal and time monotonicity for the averaged size function.

For `P : PsiData N`, a time `t`, `Υ = P.ups t`, `L = P.lEta t`, `η = vsHeight P.z t`:
* `mb_cyc_last`: the cyclic product of `s^av_{n+2}` split at the last site;
* **(a)** `mb_thetaAction`: for a kernel `|K| ≤ C_K Υ` and `|f| ≤ φ s^av_k` (`k ≥ 2`), every slot
  `j`: `|K^{(j)} f| ≤ C_K C_wc/η · φ · s^av_k` (inputs: the Schwarz bound and the symmetry of `Υ`,
  i.e. the
  fields `schwarz`, `symm` of `Contr.ContrVSInputs`);
* **(b)** `mb_remove_le` (both cyclic neighbours): removing site `j` of `x : Fin (n+3) → Fin N`
  costs one vertex: `Υ(x_j, u) · L s^av_{n+2}(x \ x_j) ≤ √C₁'' · L s^av_{n+3}(x)` for each
  cyclic neighbour `u` of `x_j` (input: the triangle bound, field `triangle`);
* **(c)** `mb_lsAv_mono`: `L_s s^av_{k,s} ≤ L_t s^av_{k,t}` if `L_t ≤ L_s` and `Υ_s ≤ Υ_t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open scoped BigOperators

variable {N : ℕ}

/-!
## The cyclic product split at the last site
-/

theorem mb_finRotate_castSucc_castSucc {n : ℕ} (e : Fin n) :
    finRotate (n + 2) e.castSucc.castSucc = e.succ.castSucc := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff]; omega)]
  simp

theorem mb_finRotate_last_castSucc (n : ℕ) :
    finRotate (n + 2) (Fin.last n).castSucc = Fin.last (n + 1) := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff])]
  simp

/-- The cyclic product of `x : Fin (n+2) → Fin N` split at the last site:
`Π_e U(x_e,x_{e+1}) = (Π_{e<n} U(x_e,x_{e+1})) U(x_n,x_{n+1}) U(x_{n+1},x_0)`. -/
theorem mb_cyc_last (U : Matrix (Fin N) (Fin N) ℝ) {n : ℕ} (x : Fin (n + 2) → Fin N) :
    ∏ e : Fin (n + 2), U (x e) (x (finRotate (n + 2) e)) =
      (∏ e : Fin n, U (x e.castSucc.castSucc) (x e.succ.castSucc)) *
        U (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) * U (x (Fin.last (n + 1))) (x 0) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, finRotate_last,
    mb_finRotate_last_castSucc]
  simp_rw [mb_finRotate_castSucc_castSucc]

variable (P : PsiData N) (t : ℝ)

/-- `s^av_{n+2}` in the split form. -/
theorem mb_sAv_last {n : ℕ} (x : Fin (n + 2) → Fin N) :
    P.sAv x t = P.lEta t ^ (-((n + 2 : ℕ) : ℝ) / 2) *
      Real.sqrt ((∏ e : Fin n, P.ups t (x e.castSucc.castSucc) (x e.succ.castSucc)) *
        P.ups t (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) *
        P.ups t (x (Fin.last (n + 1))) (x 0)) := by
  unfold PsiData.sAv
  rw [ite_eq_right (by omega), mb_cyc_last]

/-!
## Rotations
-/

/-- The rotation bringing site `j` to the last position. -/
def mbRotTo {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → Fin N) : Fin (n + 1) → Fin N :=
  fun i => x ((finRotate (n + 1) ^ ((j : ℕ) + 1)) i)

theorem mbRotTo_last {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → Fin N) :
    mbRotTo j x (Fin.last n) = x j := by
  unfold mbRotTo
  congr 1
  apply Fin.ext
  rw [contr_finRotate_pow_val, Fin.val_last]
  have := j.isLt
  rw [show n + ((j : ℕ) + 1) = (j : ℕ) + (n + 1) by ring, Nat.add_mod_right,
    Nat.mod_eq_of_lt this]

theorem mbRotTo_val {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → Fin N) (i : Fin (n + 1)) :
    mbRotTo j x i = x ⟨((i : ℕ) + (j + 1)) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
  unfold mbRotTo
  congr 1
  exact Fin.ext (contr_finRotate_pow_val _ _)

theorem mbRotTo_update {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → Fin N) (c : Fin N) :
    mbRotTo j (update x j c) = update (mbRotTo j x) (Fin.last n) c := by
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [update_self]
    unfold mbRotTo
    have : (finRotate (n + 1) ^ ((j : ℕ) + 1)) (Fin.last n) = j := by
      apply Fin.ext
      rw [contr_finRotate_pow_val, Fin.val_last]
      rw [show n + ((j : ℕ) + 1) = (j : ℕ) + (n + 1) by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt j.isLt]
    rw [this, update_self]
  · rw [update_of_ne hi]
    unfold mbRotTo
    have : (finRotate (n + 1) ^ ((j : ℕ) + 1)) i ≠ j := by
      intro h
      apply hi
      have h2 : (finRotate (n + 1) ^ ((j : ℕ) + 1)) (Fin.last n) = j := by
        apply Fin.ext
        rw [contr_finRotate_pow_val, Fin.val_last]
        rw [show n + ((j : ℕ) + 1) = (j : ℕ) + (n + 1) by ring, Nat.add_mod_right,
          Nat.mod_eq_of_lt j.isLt]
      exact (finRotate (n + 1) ^ ((j : ℕ) + 1)).injective (h.trans h2.symm)
    rw [update_of_ne this]

theorem mb_sAv_rotTo {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → Fin N) :
    P.sAv (mbRotTo j x) t = P.sAv x t :=
  contr_sAv_comp_finRotate_pow P x _ t

/-!
## (a) The `Θ̂`-action
-/

section Action

variable {d : VSData}

/-- **Kernel action on `s^av`**: if `‖K a b‖ ≤ C_K Υ(a,b)` and `‖f y‖ ≤ φ s^av_{n+2}(y)` for
all `y`, then for every slot `j` and site `x`:
`‖K^{(j)} f (x)‖ ≤ C_K C_wc/η · φ · s^av_{n+2}(x)`.
-/
theorem mb_thetaAction (hin : ContrVSInputs d P t) {n : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    {CK φ : ℝ} (hCK : 0 ≤ CK) (hφ : 0 ≤ φ) (hK : ∀ a b, ‖K a b‖ ≤ CK * P.ups t a b)
    (f : (Fin (n + 2) → Fin N) → ℂ) (hf : ∀ y, ‖f y‖ ≤ φ * P.sAv y t)
    (j : Fin (n + 2)) (x : Fin (n + 2) → Fin N) :
    ‖mbSlot K j f x‖ ≤ CK * d.Cwc / vsHeight P.z t * φ * P.sAv x t := by
  have hU := hin.nonneg
  have hsym := hin.symm
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = ∏ e : Fin n, P.ups t (mbRotTo j x e.castSucc.castSucc)
      (mbRotTo j x e.succ.castSucc) := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := hQdef ▸ Finset.prod_nonneg fun _ _ => hU _ _
  obtain ⟨u, hu⟩ : ∃ u, u = mbRotTo j x (Fin.last n).castSucc := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = mbRotTo j x 0 := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = P.lEta t ^ (-((n + 2 : ℕ) : ℝ) / 2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := hc0def ▸ Real.rpow_nonneg hin.lEta_pos.le _
  have hupd : ∀ c, P.sAv (update x j c) t =
      c0 * Real.sqrt (Q * P.ups t u c * P.ups t c w) := by
    intro c
    rw [← mb_sAv_rotTo P t j, mbRotTo_update, mb_sAv_last]
    have h1 : ∀ e : Fin n, update (mbRotTo j x) (Fin.last (n + 1)) c e.castSucc.castSucc =
        mbRotTo j x e.castSucc.castSucc :=
      fun e => update_of_ne (by simp [Fin.ext_iff]; omega) _ _
    have h2 : ∀ e : Fin n, update (mbRotTo j x) (Fin.last (n + 1)) c e.succ.castSucc =
        mbRotTo j x e.succ.castSucc :=
      fun e => update_of_ne (by simp [Fin.ext_iff]; omega) _ _
    have h3 : update (mbRotTo j x) (Fin.last (n + 1)) c (Fin.last n).castSucc = u :=
      hu ▸ update_of_ne (by simp [Fin.ext_iff]) _ _
    have h4 : update (mbRotTo j x) (Fin.last (n + 1)) c 0 = w :=
      hw ▸ update_of_ne (by simp [Fin.ext_iff]) _ _
    simp only [h1, h2, h3, h4, update_self, hQdef, hc0def]
  have hx : P.sAv x t = c0 * Real.sqrt (Q * P.ups t u (x j) * P.ups t (x j) w) := by
    have := hupd (x j)
    rwa [update_eq_self] at this
  calc ‖mbSlot K j f x‖ ≤ ∑ c, ‖K (x j) c‖ * ‖f (update x j c)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ c, CK * P.ups t (x j) c *
          (φ * (c0 * Real.sqrt (Q * P.ups t u c * P.ups t c w))) :=
        Finset.sum_le_sum fun c _ => by
          rw [← hupd c]
          exact mul_le_mul (hK _ _) (hf _) (norm_nonneg _) (mul_nonneg hCK (hU _ _))
    _ = CK * φ * c0 * Real.sqrt Q *
          ∑ c, Real.sqrt (P.ups t (x j) c * P.ups t (x j) c * P.ups t c u * P.ups t c w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        have e1 : P.ups t (x j) c = Real.sqrt (P.ups t (x j) c * P.ups t (x j) c) :=
          (Real.sqrt_mul_self (hU _ _)).symm
        rw [hsym u c]
        have e2 : Real.sqrt (Q * P.ups t c u * P.ups t c w) =
            Real.sqrt Q * Real.sqrt (P.ups t c u * P.ups t c w) := by
          rw [mul_assoc, Real.sqrt_mul hQ]
        rw [e2]
        nth_rewrite 1 [e1]
        rw [show P.ups t (x j) c * P.ups t (x j) c * P.ups t c u * P.ups t c w =
          (P.ups t (x j) c * P.ups t (x j) c) * (P.ups t c u * P.ups t c w) by ring,
          Real.sqrt_mul (mul_nonneg (hU _ _) (hU _ _))]
        ring
    _ ≤ CK * φ * c0 * Real.sqrt Q *
          (d.Cwc / vsHeight P.z t * Real.sqrt (P.ups t (x j) u * P.ups t (x j) w)) :=
        mul_le_mul_of_nonneg_left (hin.schwarz _ _ _ _)
          (mul_nonneg (mul_nonneg (mul_nonneg hCK hφ) hc0) (Real.sqrt_nonneg _))
    _ = CK * d.Cwc / vsHeight P.z t * φ * P.sAv x t := by
        rw [hx, hsym (x j) u, mul_assoc Q, Real.sqrt_mul hQ]
        ring

end Action

/-!
## (b) Removing a site
-/

section Remove

variable {d : VSData}

/-- Removal at the last site: `Υ(v,u) L s^av_{n+2}(init x) ≤ √C₁'' L s^av_{n+3}(x)` with
`u = x_{n+1}`, `v = x_{n+2}`, and the same with `Υ(v, x_0)`. -/
theorem mb_remove_last (hin : ContrVSInputs d P t) {n : ℕ} (x : Fin (n + 3) → Fin N) :
    P.ups t (x (Fin.last (n + 2))) (x (Fin.last (n + 1)).castSucc) *
        (P.lEta t * P.sAv (Fin.init x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) ∧
    P.ups t (x (Fin.last (n + 2))) (x 0) * (P.lEta t * P.sAv (Fin.init x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  set U := P.ups t with hUdef
  set L := P.lEta t with hLdef
  have hL : 0 < L := hin.lEta_pos
  have hU : ∀ a b, 0 ≤ U a b := hin.nonneg
  have hsym : ∀ a b, U a b = U b a := hin.symm
  set u := x (Fin.last (n + 1)).castSucc
  set v := x (Fin.last (n + 2))
  set w := x 0
  set R := (∏ e : Fin n, U (x e.castSucc.castSucc.castSucc) (x e.succ.castSucc.castSucc)) *
    U (x (Fin.last n).castSucc.castSucc) (x (Fin.last (n + 1)).castSucc)
  have hR : 0 ≤ R := mul_nonneg (Finset.prod_nonneg fun _ _ => hU _ _) (hU _ _)
  have hy : P.sAv (Fin.init x) t = L ^ (-((n + 2 : ℕ) : ℝ) / 2) * Real.sqrt (R * U u w) := by
    rw [mb_sAv_last]
    simp only [Fin.init]
    congr 2
  have hx : P.sAv x t = L ^ (-((n + 3 : ℕ) : ℝ) / 2) * Real.sqrt (R * U u v * U v w) := by
    rw [mb_sAv_last, Fin.prod_univ_castSucc]
    rfl
  have hpow : L ^ (-((n + 2 : ℕ) : ℝ) / 2) = L ^ (-((n + 3 : ℕ) : ℝ) / 2) * Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    congr 1
    push_cast
    ring
  set c := L * L ^ (-((n + 3 : ℕ) : ℝ) / 2)
  have hc : 0 ≤ c := mul_nonneg hL.le (Real.rpow_nonneg hL.le _)
  have key : ∀ a b, U v a * U a b ≤ d.C1pp / L * U v b → ∀ p, (U v p = U v a) →
      U v p * (L * (L ^ (-((n + 3 : ℕ) : ℝ) / 2) * Real.sqrt L * Real.sqrt (R * U a b))) ≤
        Real.sqrt d.C1pp * (c * Real.sqrt (R * U a v * U v b)) := by
    intro a b htri p hp
    rw [hp]
    have hC := hin.lEta_pos
    have hlhs : U v a * (L * (L ^ (-((n + 3 : ℕ) : ℝ) / 2) * Real.sqrt L * Real.sqrt (R * U a b)))
        = c * Real.sqrt (U v a * U v a * L * (R * U a b)) := by
      have e1 : Real.sqrt (U v a * U v a * L * (R * U a b)) =
          U v a * Real.sqrt L * Real.sqrt (R * U a b) := by
        rw [Real.sqrt_mul (mul_nonneg (mul_self_nonneg _) hL.le),
          Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (hU _ _)]
      rw [e1]
      ring
    have hrhs : Real.sqrt d.C1pp * (c * Real.sqrt (R * U a v * U v b)) =
        c * Real.sqrt (d.C1pp * (R * U a v * U v b)) := by
      rw [Real.sqrt_mul' _ (mul_nonneg (mul_nonneg hR (hU _ _)) (hU _ _))]
      ring
    rw [hlhs, hrhs]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hc
    have h1 : U v a * U a b * L ≤ d.C1pp * U v b := by
      have := mul_le_mul_of_nonneg_right htri hL.le
      calc U v a * U a b * L ≤ d.C1pp / L * U v b * L := this
        _ = d.C1pp * U v b := by field_simp
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (hU v a) hR)
    rw [hsym a v]
    nlinarith [h2, hU v a, hR]
  constructor
  · have := key u w (hin.triangle v u w) _ rfl
    rw [hy, hpow, hx]
    simpa [c, mul_assoc] using this
  · have h := key w u (hin.triangle v w u) _ rfl
    rw [hy, hpow, hx]
    have e1 : R * U u w = R * U w u := by rw [hsym]
    have e2 : R * U u v * U v w = R * U w v * U v u := by
      rw [hsym u v, hsym v w]
      ring
    rw [e1, e2]
    simpa [c, mul_assoc] using h

/-- The rotated vector `mbRotTo j x` with its last site removed is a rotation of
`Fin.removeNth j x`; hence `s^av(removeNth j x) = s^av(init (mbRotTo j x))`. -/
theorem mb_sAv_removeNth {n : ℕ} (j : Fin (n + 3)) (x : Fin (n + 3) → Fin N) :
    P.sAv (Fin.removeNth j x) t = P.sAv (Fin.init (mbRotTo j x)) t := by
  symm
  refine contr_sAv_rotate P (Fin.removeNth j x) (Fin.init (mbRotTo j x)) j (fun m hm => ?_) t
  simp only [Fin.init, Fin.removeNth]
  rw [mbRotTo_val]
  congr 1
  apply Fin.ext
  have hj := j.isLt
  by_cases h : m + (j : ℕ) < n + 2
  · have hmod : (m + (j : ℕ)) % (n + 2) = m + j := Nat.mod_eq_of_lt h
    rw [Fin.succAbove_of_le_castSucc]
    · simp only [Fin.val_succ, hmod, Fin.val_castSucc]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.le_def]
      simp only [Fin.val_castSucc, hmod]
      omega
  · have hmod : (m + (j : ℕ)) % (n + 2) = m + j - (n + 2) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Fin.succAbove_of_castSucc_lt]
    · simp only [Fin.val_castSucc, hmod]
      rw [show (m : ℕ) + ((j : ℕ) + 1) = (m + j + 1 - (n + 3)) + (n + 3) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.lt_def]
      simp only [Fin.val_castSucc, hmod]
      omega

/-- The cyclic predecessor of site `j` in `Fin (n+3)`. -/
def mbPrev {n : ℕ} (j : Fin (n + 3)) : Fin (n + 3) := ⟨((j : ℕ) + (n + 2)) % (n + 3),
  Nat.mod_lt _ (by omega)⟩

/-- The cyclic successor of site `j` in `Fin (n+3)`. -/
def mbNext {n : ℕ} (j : Fin (n + 3)) : Fin (n + 3) := ⟨((j : ℕ) + 1) % (n + 3),
  Nat.mod_lt _ (by omega)⟩

/-- **Removing one site**: removing site `j` of `x : Fin (n+3) → Fin N`:
`Υ(x_j, x_{j-1}) L s^av_{n+2}(x \ x_j) ≤ √C₁'' L s^av_{n+3}(x)` and the same with the successor
`x_{j+1}` (cyclic).
-/
theorem mb_remove_le {d : VSData} (hin : ContrVSInputs d P t) {n : ℕ} (j : Fin (n + 3))
    (x : Fin (n + 3) → Fin N) :
    P.ups t (x j) (x (mbPrev j)) * (P.lEta t * P.sAv (Fin.removeNth j x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) ∧
    P.ups t (x j) (x (mbNext j)) * (P.lEta t * P.sAv (Fin.removeNth j x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  have h := mb_remove_last P t hin (mbRotTo j x)
  rw [mbRotTo_last, mbRotTo_val, mbRotTo_val, mb_sAv_rotTo] at h
  rw [mb_sAv_removeNth]
  refine ⟨?_, ?_⟩
  · convert h.1 using 4
    apply Fin.ext
    simp only [mbPrev, Fin.val_castSucc, Fin.val_last]
    congr 1
    omega
  · convert h.2 using 4
    apply Fin.ext
    simp [mbNext]

end Remove

/-!
## (c) Monotonicity in time
-/

/-- **Monotonicity in time of `L s^av`**: if `0 < L_t ≤ L_s` and `0 ≤ Υ_s ≤ Υ_t` entrywise, then
`L_s s^av_{n+2,s}(x) ≤ L_t s^av_{n+2,t}(x)`.
-/
theorem mb_lsAv_mono {s : ℝ} (hLt : 0 < P.lEta t) (hL : P.lEta t ≤ P.lEta s)
    (hU0 : ∀ a b, 0 ≤ P.ups s a b) (hU : ∀ a b, P.ups s a b ≤ P.ups t a b) {n : ℕ}
    (x : Fin (n + 2) → Fin N) :
    P.lEta s * P.sAv x s ≤ P.lEta t * P.sAv x t := by
  unfold PsiData.sAv
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hLs : 0 < P.lEta s := hLt.trans_le hL
  rw [← mul_assoc, ← mul_assoc]
  have e : ∀ L : ℝ, 0 < L → L * L ^ (-((n + 2 : ℕ) : ℝ) / 2) = L ^ (-(n : ℝ) / 2) := by
    intro L hL0
    rw [show -(n : ℝ) / 2 = 1 + -((n + 2 : ℕ) : ℝ) / 2 by push_cast; ring,
      Real.rpow_add hL0, Real.rpow_one]
  rw [e _ hLs, e _ hLt]
  refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hLt hL (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)) (Real.sqrt_le_sqrt (Finset.prod_le_prod₀ (fun _ _ => hU0 _ _)
      fun _ _ => hU _ _)) (Real.sqrt_nonneg _) (Real.rpow_nonneg hLt.le _)

end BlockBand.Native.ErdosRiabov.MBound
