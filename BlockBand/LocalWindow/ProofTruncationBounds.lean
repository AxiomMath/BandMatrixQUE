module

public import BlockBand.LocalWindow.ProofTruncation
public import BlockBand.DeterminantScore.MinorTailInverseTrace

/-!
# Norm and Lipschitz bounds for the truncated deformation

With `‖C‖ ≤ c` (both `C` and `C*`, as Euclidean maps),
`‖g_ε(H_R - E)‖ ≤ ε⁻¹`, `‖g_ε(H_R - E) - g_ε(H_R - e)‖ ≤ |E - e|/ε²`, hence
`‖F̂(E) - F̂(e)‖ ≤ c²|E - e|/ε²`, and the truncated Schur complements at `E` and at a grid
point `e` differ by a perturbation of rank `0` and size `(c²/ε² + 1)|E - e|`
(`isPerturbation_grid`). The Gaussian norm event that bounds `‖C‖` is proved separately
(`normEvent_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCount

open Matrix Module Finset BlockBand.DeterminantScore.MinorTailInverse
open scoped InnerProductSpace

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-!
## The scalar truncated inverse
-/

theorem abs_truncInv_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |truncInv ε x| ≤ ε⁻¹ := by
  unfold truncInv
  split_ifs with h
  · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ε ^ 2), div_le_iff₀ (by positivity)]
    calc |x| ≤ ε := h
      _ = ε⁻¹ * ε ^ 2 := by field_simp
  · rw [abs_inv]
    exact inv_anti₀ hε (le_of_lt (lt_of_not_ge h))

theorem abs_inv_sub_inv_le {ε a b : ℝ} (hε : 0 < ε) (ha : ε ≤ |a|) (hb : ε ≤ |b|) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / ε ^ 2 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, abs_zero] at ha; linarith
  have hb0 : b ≠ 0 := fun h => by rw [h, abs_zero] at hb; linarith
  rw [inv_sub_inv ha0 hb0, abs_div, abs_mul, abs_sub_comm b a]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  rw [sq]; exact mul_le_mul ha hb hε.le (abs_nonneg _)

/-- `g_ε` is `ε⁻²`-Lipschitz. -/
theorem abs_truncInv_sub_le {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |truncInv ε x - truncInv ε y| ≤ |x - y| / ε ^ 2 := by
  have hin : ∀ u v : ℝ, |u| ≤ ε → |v| ≤ ε → |truncInv ε u - truncInv ε v| ≤ |u - v| / ε ^ 2 := by
    intro u v hu hv
    unfold truncInv; simp only [hu, hv, ↓reduceIte]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0:ℝ) < ε ^ 2)]
  have hbd : ∀ s : ℝ, |s| = ε → truncInv ε s = s⁻¹ := by
    intro s hs
    unfold truncInv; simp only [hs.le, ↓reduceIte]
    have hs0 : s ≠ 0 := fun h => by rw [h, abs_zero] at hs; linarith
    rw [← hs, sq_abs, sq, div_mul_eq_div_div, div_self hs0, one_div]
  have hout : ∀ u v : ℝ, ε ≤ |u| → ε ≤ |v| → |truncInv ε u - truncInv ε v| ≤ |u - v| / ε ^ 2 := by
    intro u v hu hv
    have eu : truncInv ε u = u⁻¹ := by
      rcases eq_or_lt_of_le hu with h | h
      · exact hbd u h.symm
      · unfold truncInv; simp only [not_le.mpr h, ↓reduceIte]
    have ev : truncInv ε v = v⁻¹ := by
      rcases eq_or_lt_of_le hv with h | h
      · exact hbd v h.symm
      · unfold truncInv; simp only [not_le.mpr h, ↓reduceIte]
    rw [eu, ev]; exact abs_inv_sub_inv_le hε hu hv
  -- mixed case through the boundary point `s = ±ε` between `u` and `v`
  have hmix : ∀ u v : ℝ, |u| ≤ ε → ε < |v| →
      |truncInv ε u - truncInv ε v| ≤ |u - v| / ε ^ 2 := by
    intro u v hu hv
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    rcases le_or_gt 0 v with hv0 | hv0
    · rw [abs_of_nonneg hv0] at hv
      have h1 := hin u ε hu (by rw [abs_of_pos hε])
      have h2 := hout ε v (by rw [abs_of_pos hε]) (by rw [abs_of_nonneg hv0]; exact hv.le)
      calc |truncInv ε u - truncInv ε v|
          ≤ |truncInv ε u - truncInv ε ε| + |truncInv ε ε - truncInv ε v| := abs_sub_le _ _ _
        _ ≤ |u - ε| / ε ^ 2 + |ε - v| / ε ^ 2 := add_le_add h1 h2
        _ = |u - v| / ε ^ 2 := by
          rw [abs_of_nonpos (by linarith : u - ε ≤ 0), abs_of_nonpos (by linarith : ε - v ≤ 0),
            abs_of_nonpos (by linarith : u - v ≤ 0)]; ring
    · rw [abs_of_neg hv0] at hv
      have h1 := hin u (-ε) hu (by rw [abs_neg, abs_of_pos hε])
      have h2 := hout (-ε) v (by rw [abs_neg, abs_of_pos hε]) (by rw [abs_of_neg hv0]; linarith)
      calc |truncInv ε u - truncInv ε v|
          ≤ |truncInv ε u - truncInv ε (-ε)| + |truncInv ε (-ε) - truncInv ε v| :=
            abs_sub_le _ _ _
        _ ≤ |u - -ε| / ε ^ 2 + |-ε - v| / ε ^ 2 := add_le_add h1 h2
        _ = |u - v| / ε ^ 2 := by
          rw [abs_of_nonneg (by linarith : 0 ≤ u - -ε), abs_of_nonneg (by linarith : 0 ≤ -ε - v),
            abs_of_nonneg (by linarith : 0 ≤ u - v)]; ring
  rcases le_or_gt |x| ε with hx | hx <;> rcases le_or_gt |y| ε with hy | hy
  · exact hin x y hx hy
  · exact hmix x y hx hy
  · rw [abs_sub_comm, abs_sub_comm x y]; exact hmix y x hy hx
  · exact hout x y hx.le hy.le

/-!
## Spectral conjugates
-/

section Conj

variable {α : Type} [Fintype α] [DecidableEq α]

theorem norm_toE_diagonal_le (d : α → ℂ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, ‖d j‖ ≤ M)
    (w : EuclideanSpace ℂ α) : ‖T (diagonal d) w‖ ≤ M * ‖w‖ := by
  have hsq : ‖T (diagonal d) w‖ ^ 2 ≤ (M * ‖w‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [show (T (diagonal d) w) j = d j * w j by
      simp [toE_apply, mulVec_diagonal], norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM j) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- `‖U diag(d) U* x‖ ≤ M‖x‖` for a unitary `U` and `|d_j| ≤ M`. -/
theorem norm_toE_conj_le (U : Matrix.unitaryGroup α ℂ) (d : α → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, ‖d j‖ ≤ M) (x : EuclideanSpace ℂ α) :
    ‖T ((U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ)) x‖ ≤ M * ‖x‖ := by
  have hU : (U : Matrix α α ℂ)ᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hU' : (star (U : Matrix α α ℂ))ᴴ * star (U : Matrix α α ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose, star_star]; exact Unitary.coe_mul_star_self _
  rw [← toE_toE, ← toE_toE, norm_toE_isometry hU, ← norm_toE_isometry hU' x]
  exact norm_toE_diagonal_le d hM0 hM _

end Conj

/-!
## Bounds for `g_ε(H - E)` and `F̂(E)`
-/

section Bounds

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem norm_truncResolvent_le {H : Matrix α α ℂ} (hH : H.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (E : ℝ) (x : EuclideanSpace ℂ α) : ‖T (truncResolvent ε H E) x‖ ≤ ε⁻¹ * ‖x‖ := by
  unfold truncResolvent
  simp only [hH, ↓reduceDIte]
  exact norm_toE_conj_le _ _ (by positivity) (fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_truncInv_le hε _) x

theorem norm_truncResolvent_sub_le {H : Matrix α α ℂ} (hH : H.IsHermitian) {ε : ℝ}
    (hε : 0 < ε) (E e : ℝ) (x : EuclideanSpace ℂ α) :
    ‖T (truncResolvent ε H E - truncResolvent ε H e) x‖ ≤ |E - e| / ε ^ 2 * ‖x‖ := by
  unfold truncResolvent
  simp only [hH, ↓reduceDIte]
  rw [conj_sub_conj]
  refine norm_toE_conj_le _ _ (by positivity) (fun j => ?_) x
  rw [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have := abs_truncInv_sub_le hε (hH.eigenvalues j - E) (hH.eigenvalues j - e)
  rwa [show hH.eigenvalues j - E - (hH.eigenvalues j - e) = -(E - e) by ring, abs_neg] at this

/-- `‖F̂(E) - F̂(e)‖ ≤ c² |E - e| / ε²` when `‖C‖, ‖C*‖ ≤ c` as Euclidean maps. -/
theorem norm_truncF_sub_le {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hC : ∀ v, ‖T C v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T Cᴴ w‖ ≤ c * ‖w‖) (E e : ℝ)
    (x : EuclideanSpace ℂ β) :
    ‖T (truncF ε H_R C V E - truncF ε H_R C V e) x‖ ≤ c ^ 2 * (|E - e| / ε ^ 2) * ‖x‖ := by
  have hd : truncF ε H_R C V E - truncF ε H_R C V e =
      Cᴴ * (truncResolvent ε H_R e - truncResolvent ε H_R E) * C := by
    unfold truncF; rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hd, ← toE_toE, ← toE_toE]
  calc ‖T Cᴴ (T (truncResolvent ε H_R e - truncResolvent ε H_R E) (T C x))‖
      ≤ c * ‖T (truncResolvent ε H_R e - truncResolvent ε H_R E) (T C x)‖ := hC' _
    _ ≤ c * (|e - E| / ε ^ 2 * ‖T C x‖) :=
        mul_le_mul_of_nonneg_left (norm_truncResolvent_sub_le hH hε e E _) hc
    _ ≤ c * (|e - E| / ε ^ 2 * (c * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC x) (by positivity)) hc
    _ = c ^ 2 * (|E - e| / ε ^ 2) * ‖x‖ := by rw [abs_sub_comm]; ring

/-- `‖F̂(E)‖ ≤ ‖V‖ + c²/ε`. -/
theorem norm_truncF_le {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {ε c v : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hC : ∀ y, ‖T C y‖ ≤ c * ‖y‖) (hC' : ∀ w, ‖T Cᴴ w‖ ≤ c * ‖w‖)
    (hV : ∀ y, ‖T V y‖ ≤ v * ‖y‖) (E : ℝ) (x : EuclideanSpace ℂ β) :
    ‖T (truncF ε H_R C V E) x‖ ≤ (v + c ^ 2 / ε) * ‖x‖ := by
  unfold truncF
  rw [map_sub, LinearMap.sub_apply, ← toE_toE, ← toE_toE]
  calc ‖T V x - T Cᴴ (T (truncResolvent ε H_R E) (T C x))‖
      ≤ ‖T V x‖ + ‖T Cᴴ (T (truncResolvent ε H_R E) (T C x))‖ := norm_sub_le _ _
    _ ≤ v * ‖x‖ + c * (ε⁻¹ * (c * ‖x‖)) := by
        refine add_le_add (hV x) ((hC' _).trans (mul_le_mul_of_nonneg_left ?_ hc))
        exact (norm_truncResolvent_le hH hε E _).trans
          (mul_le_mul_of_nonneg_left (hC x) (by positivity))
    _ = (v + c ^ 2 / ε) * ‖x‖ := by field_simp

/-- **Grid move**: the truncated Schur complements at `E` and `e` differ by a perturbation of
rank `0` and size `(c²/ε² + 1)|E - e|`. -/
theorem isPerturbation_grid {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V G : Matrix β β ℂ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hC : ∀ y, ‖T C y‖ ≤ c * ‖y‖) (hC' : ∀ w, ‖T Cᴴ w‖ ≤ c * ‖w‖) (E e : ℝ) :
    IsPerturbation (truncF ε H_R C V e + G - (e : ℂ) • 1) (truncF ε H_R C V E + G - (E : ℂ) • 1)
      0 ((c ^ 2 / ε ^ 2 + 1) * |E - e|) := by
  refine isPerturbation_of_norm fun x => ?_
  have hd : truncF ε H_R C V E + G - (E : ℂ) • 1 - (truncF ε H_R C V e + G - (e : ℂ) • 1) =
      (truncF ε H_R C V E - truncF ε H_R C V e) - ((E - e : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_sub, sub_smul]; abel
  rw [hd, map_sub, LinearMap.sub_apply]
  have h1 : ‖T (((E - e : ℝ) : ℂ) • (1 : Matrix β β ℂ)) x‖ = |E - e| * ‖x‖ := by
    rw [toE_apply, Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.toLp_smul, WithLp.toLp_ofLp,
      norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖T (truncF ε H_R C V E - truncF ε H_R C V e) x -
        T (((E - e : ℝ) : ℂ) • (1 : Matrix β β ℂ)) x‖
      ≤ ‖T (truncF ε H_R C V E - truncF ε H_R C V e) x‖ +
          ‖T (((E - e : ℝ) : ℂ) • (1 : Matrix β β ℂ)) x‖ := norm_sub_le _ _
    _ ≤ c ^ 2 * (|E - e| / ε ^ 2) * ‖x‖ + |E - e| * ‖x‖ :=
        add_le_add (norm_truncF_sub_le hH C V hε hc hC hC' E e x) h1.le
    _ = (c ^ 2 / ε ^ 2 + 1) * |E - e| * ‖x‖ := by ring

end Bounds

end BlockBand.LocalWindow.ProofCount
