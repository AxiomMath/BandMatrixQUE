module

public import Mathlib

/-!
# Imaginary-part margins of finite complex matrices

A matrix `N` has imaginary margin `η` if `η ‖v‖² ≤ Im ⟨v, N v⟩` for all `v`. A positive margin
makes `N` invertible with `|(N⁻¹)_{ab}| ≤ η⁻¹`, and is preserved by adding Hermitian matrices.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `N` has imaginary margin `η`: `η ‖v‖² ≤ Im ⟨v, N v⟩` for every `v : n → ℂ`. -/
def HasImMargin (η : ℝ) (N : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, η * (star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ (N *ᵥ v)).im

omit [DecidableEq n] in
/-- `‖v‖² = Re ⟨v, v⟩` as a sum of squared moduli. -/
theorem re_star_dotProduct_self (v : n → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp

omit [DecidableEq n] in
theorem norm_sq_le_re_star_dotProduct_self (v : n → ℂ) (i : n) :
    ‖v i‖ ^ 2 ≤ (star v ⬝ᵥ v).re := by
  rw [re_star_dotProduct_self]
  exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

omit [DecidableEq n] in
/-- A Hermitian quadratic form is real. -/
theorem im_star_dotProduct_mulVec_hermitian {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (v : n → ℂ) : (star v ⬝ᵥ (B *ᵥ v)).im = 0 :=
  Complex.conj_eq_iff_im.mp (hB.star_dotProduct_mulVec_comm v v)

omit [DecidableEq n] in
/-- Adding a Hermitian matrix keeps the imaginary margin. -/
theorem HasImMargin.add_hermitian {η : ℝ} {N B : Matrix n n ℂ} (h : HasImMargin η N)
    (hB : B.IsHermitian) : HasImMargin η (N + B) := by
  intro v
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_im, im_star_dotProduct_mulVec_hermitian hB,
    add_zero]
  exact h v

omit [DecidableEq n] in
/-- Adding a Hermitian matrix on the left keeps the imaginary margin. -/
theorem HasImMargin.hermitian_add {η : ℝ} {N B : Matrix n n ℂ} (h : HasImMargin η N)
    (hB : B.IsHermitian) : HasImMargin η (B + N) := by
  rw [add_comm]
  exact h.add_hermitian hB

omit [DecidableEq n] in
/-- A positive margin forces a trivial kernel. -/
theorem HasImMargin.eq_zero_of_mulVec_eq_zero {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ}
    (h : HasImMargin η N) {v : n → ℂ} (hv : N *ᵥ v = 0) : v = 0 := by
  have h1 := h v
  rw [hv, dotProduct_zero, Complex.zero_im] at h1
  have h2 : (star v ⬝ᵥ v).re ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hη hc
    linarith
  funext i
  have h3 := norm_sq_le_re_star_dotProduct_self v i
  have h4 : ‖v i‖ ^ 2 = 0 := le_antisymm (h3.trans h2) (sq_nonneg _)
  simpa using h4

/-- A matrix with positive imaginary margin is invertible. -/
theorem HasImMargin.isUnit {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ} (h : HasImMargin η N) :
    IsUnit N := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have : N *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (h.eq_zero_of_mulVec_eq_zero hη this)

/-- Determinant form of `HasImMargin.isUnit`. -/
theorem HasImMargin.isUnit_det {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ} (h : HasImMargin η N) :
    IsUnit N.det :=
  (Matrix.isUnit_iff_isUnit_det N).mp (h.isUnit hη)

/-- Entry bound for the inverse: `|(N⁻¹)_{ab}| ≤ η⁻¹`. -/
theorem HasImMargin.norm_inv_apply_le {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ}
    (h : HasImMargin η N) (a b : n) : ‖N⁻¹ a b‖ ≤ η⁻¹ := by
  set u : n → ℂ := N⁻¹ *ᵥ Pi.single b 1 with hu
  have hNu : N *ᵥ u = Pi.single b 1 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (h.isUnit_det hη), Matrix.one_mulVec]
  have hua : u a = N⁻¹ a b := by
    rw [hu]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hq : star u ⬝ᵥ (N *ᵥ u) = star (u b) := by
    rw [hNu, dotProduct_single, mul_one]
    rfl
  have h1 := h u
  rw [hq] at h1
  set S := (star u ⬝ᵥ u).re
  have hx : (star (u b)).im ≤ ‖u b‖ := by
    have := Complex.abs_im_le_norm (star (u b))
    rw [norm_star] at this
    exact (le_abs_self _).trans this
  have hxS : ‖u b‖ ^ 2 ≤ S := norm_sq_le_re_star_dotProduct_self u b
  have hyS : ‖u a‖ ^ 2 ≤ S := norm_sq_le_re_star_dotProduct_self u a
  have hx0 : 0 ≤ ‖u b‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖u a‖ := norm_nonneg _
  have hηS : η * S ≤ ‖u b‖ := h1.trans hx
  have hηx : η * ‖u b‖ ≤ 1 := by
    rcases hx0.lt_or_eq with hpos | hzero
    · have : η * ‖u b‖ * ‖u b‖ ≤ 1 * ‖u b‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    · rw [← hzero, mul_zero]
      exact zero_le_one
  have hηy : (η * ‖u a‖) ^ 2 ≤ 1 := by
    have : (η * ‖u a‖) ^ 2 ≤ η * (η * S) := by
      rw [mul_pow, sq η, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyS hη.le) hη.le
    nlinarith
  have hηy' : η * ‖u a‖ ≤ 1 := by
    nlinarith [mul_nonneg hη.le hy0]
  rw [← hua]
  calc ‖u a‖ = η⁻¹ * (η * ‖u a‖) := by field_simp
    _ ≤ η⁻¹ * 1 := mul_le_mul_of_nonneg_left hηy' (inv_nonneg.2 hη.le)
    _ = η⁻¹ := mul_one _

/-- Trace bound: `|Tr(Q N⁻¹)| ≤ η⁻¹ Σ_{a,b} |Q_{ab}|`. -/
theorem HasImMargin.norm_trace_mul_inv_le {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ}
    (h : HasImMargin η N) (Q : Matrix n n ℂ) :
    ‖(Q * N⁻¹).trace‖ ≤ (∑ a, ∑ b, ‖Q a b‖) * η⁻¹ := by
  rw [Matrix.trace, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h.norm_inv_apply_le hη b a) (norm_nonneg _)

/-- Matrix inversion (`Matrix.inv`, the nonsingular inverse, `0` on singular matrices) is
Borel measurable. -/
theorem measurable_matrix_inv : Measurable (fun A : Matrix n n ℂ => A⁻¹) := by
  have h : (fun A : Matrix n n ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (measurable_inv.comp (Continuous.matrix_det continuous_id).measurable).smul
    (Continuous.matrix_adjugate continuous_id).measurable

end BlockBand.Wegner
