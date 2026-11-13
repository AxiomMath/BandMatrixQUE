module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Palm.RegularityCertificate

/-!
# Coarse relative local law: finite Hermitian resolvent algebra

Arbitrary finite index type, arbitrary Hermitian `H`, arbitrary spectral parameter
`w` with `Im w ≠ 0`. No measure, no limit and no norm bound on `H`. Proved here:
the Euclidean squared norm `nsq`, finite Cauchy–Schwarz, the Hermitian lower bound
`(Im w)² ‖x‖² ≤ ‖(H - w) x‖²`, invertibility, the operator bound
`‖(H-w)⁻¹ y‖ ≤ |Im w|⁻¹ ‖y‖`, the resolvent identity, and the exact directional
Ward identity `Im(q*(H-w)⁻¹q) = Im w ‖(H-w)⁻¹q‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open Matrix BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean norm `Σ_k |x_k|²` (so `l2Norm x = √(nsq x)`). -/
def nsq (x : ι → ℂ) : ℝ := ∑ k, ‖x k‖ ^ 2

theorem nsq_nonneg (x : ι → ℂ) : 0 ≤ nsq x :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem l2Norm_eq_sqrt_nsq (x : ι → ℂ) : l2Norm x = Real.sqrt (nsq x) := rfl

theorem nsq_eq_euclidean (x : ι → ℂ) : nsq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem star_dotProduct_self_eq (x : ι → ℂ) : star x ⬝ᵥ x = (nsq x : ℂ) := by
  unfold nsq dotProduct
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.star_apply, ← Complex.mul_conj', mul_comm]
  rfl

/-- Finite Cauchy–Schwarz for the sesquilinear dot product. -/
theorem norm_star_dotProduct_sq_le (x y : ι → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ nsq x * nsq y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 y : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm] at h
  rw [nsq_eq_euclidean, nsq_eq_euclidean, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem nsq_smul (c : ℂ) (x : ι → ℂ) : nsq (c • x) = ‖c‖ ^ 2 * nsq x := by
  unfold nsq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- Triangle inequality for `√nsq`. -/
theorem sqrt_nsq_add_le (x y : ι → ℂ) :
    Real.sqrt (nsq (x + y)) ≤ Real.sqrt (nsq x) + Real.sqrt (nsq y) := by
  have h := norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)
  rw [← WithLp.toLp_add] at h
  rw [nsq_eq_euclidean, nsq_eq_euclidean, nsq_eq_euclidean,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact h

/-- A Hermitian quadratic form is real. -/
theorem hermitian_quad_im_eq_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  have h := hH.star_dotProduct_mulVec_comm x x
  have := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

variable [DecidableEq ι]

/-- Hermitian lower bound `(Im w)² ‖x‖² ≤ ‖(H - w)x‖²`. -/
theorem hermitian_shift_lower {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (w : ℂ) (x : ι → ℂ) :
    w.im ^ 2 * nsq x ≤ nsq ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x) := by
  have hdot : star x ⬝ᵥ ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x) =
      star x ⬝ᵥ (H *ᵥ x) - w * (nsq x : ℂ) := by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq, smul_eq_mul]
  have him : (star x ⬝ᵥ ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x)).im = -(w.im * nsq x) := by
    rw [hdot, Complex.sub_im, hermitian_quad_im_eq_zero hH, Complex.mul_im,
      Complex.ofReal_im, Complex.ofReal_re]
    ring
  have hcs := norm_star_dotProduct_sq_le x ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x)
  have hle : (w.im * nsq x) ^ 2 ≤
      ‖star x ⬝ᵥ ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x)‖ ^ 2 := by
    have h1 := Complex.abs_im_le_norm (star x ⬝ᵥ ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x))
    rw [him, abs_neg] at h1
    calc (w.im * nsq x) ^ 2 = |w.im * nsq x| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hx := nsq_nonneg x
  have hy := nsq_nonneg ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x)
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hy
  · have : w.im ^ 2 * nsq x * nsq x ≤ nsq ((H - w • (1 : Matrix ι ι ℂ)) *ᵥ x) * nsq x := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- `H - w` is invertible for Hermitian `H` and non-real `w`. -/
theorem hermitian_shift_det_isUnit {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) : IsUnit (H - w • (1 : Matrix ι ι ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hl := hermitian_shift_lower hH w v
  rw [hzero] at hl
  have h0 : nsq (0 : ι → ℂ) = 0 := by simp [nsq]
  rw [h0] at hl
  have hpos : 0 < nsq v := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    have : 0 < ‖v k‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this
      (Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ k))
  have : 0 < w.im ^ 2 * nsq v := mul_pos (by positivity) hpos
  linarith

theorem hermitian_shift_mul_inv {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    (H - w • (1 : Matrix ι ι ℂ)) * (H - w • (1 : Matrix ι ι ℂ))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (hermitian_shift_det_isUnit hH hw)

theorem hermitian_shift_inv_mul {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    (H - w • (1 : Matrix ι ι ℂ))⁻¹ * (H - w • (1 : Matrix ι ι ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ (hermitian_shift_det_isUnit hH hw)

/-- Operator bound `‖(H-w)⁻¹ y‖² ≤ (Im w)⁻² ‖y‖²`. -/
theorem hermitian_resolvent_nsq_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (y : ι → ℂ) :
    nsq ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y) ≤ (w.im ^ 2)⁻¹ * nsq y := by
  have hl := hermitian_shift_lower hH w ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y)
  rw [mulVec_mulVec, hermitian_shift_mul_inv hH hw, one_mulVec] at hl
  have hw2 : 0 < w.im ^ 2 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hw2, mul_comm]
  exact hl

/-- Conjugate transpose of the resolvent. -/
theorem hermitian_resolvent_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (w : ℂ) :
    ((H - w • (1 : Matrix ι ι ℂ))⁻¹)ᴴ = (H - (conj w) • (1 : Matrix ι ι ℂ))⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hH.eq]
  rfl

/-- Resolvent identity `R(w) - R(w') = (w - w') R(w) R(w')`. -/
theorem hermitian_resolvent_sub {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w w' : ℂ}
    (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    (H - w • (1 : Matrix ι ι ℂ))⁻¹ - (H - w' • (1 : Matrix ι ι ℂ))⁻¹ =
      (w - w') • ((H - w • (1 : Matrix ι ι ℂ))⁻¹ * (H - w' • (1 : Matrix ι ι ℂ))⁻¹) := by
  have hu : IsUnit (H - w • (1 : Matrix ι ι ℂ)) ↔ IsUnit (H - w' • (1 : Matrix ι ι ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det]
    exact ⟨fun _ => hermitian_shift_det_isUnit hH hw', fun _ => hermitian_shift_det_isUnit hH hw⟩
  rw [Matrix.inv_sub_inv hu]
  have : (H - w' • (1 : Matrix ι ι ℂ)) - (H - w • (1 : Matrix ι ι ℂ)) =
      (w - w') • (1 : Matrix ι ι ℂ) := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Directional Ward identity `Im(q*(H-w)⁻¹q) = Im w ‖(H-w)⁻¹ q‖²`. -/
theorem hermitian_resolvent_quad_im {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (q : ι → ℂ) :
    (star q ⬝ᵥ ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q)).im =
      w.im * nsq ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q) := by
  set R := (H - w • (1 : Matrix ι ι ℂ))⁻¹ with hR
  have hwc : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  -- R* - R = (conj w - w) R* R
  have hsub := hermitian_resolvent_sub hH hwc hw
  rw [← hermitian_resolvent_conjTranspose hH w] at hsub
  have hq : star q ⬝ᵥ ((Rᴴ - R) *ᵥ q) = (conj w - w) * (nsq (R *ᵥ q) : ℂ) := by
    rw [hsub, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
      ← star_mulVec, star_dotProduct_self_eq]
  have hstar : star q ⬝ᵥ (Rᴴ *ᵥ q) = star (star q ⬝ᵥ (R *ᵥ q)) := by
    symm
    rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]
  rw [sub_mulVec, dotProduct_sub, hstar] at hq
  have him := congrArg Complex.im hq
  rw [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im] at him
  linarith

omit [DecidableEq ι] in
/-- Quadratic-form bound from a squared operator bound. -/
theorem norm_quad_le_of_nsq_le (A : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ y : ι → ℂ, nsq (A *ᵥ y) ≤ C ^ 2 * nsq y) (q : ι → ℂ) :
    ‖star q ⬝ᵥ (A *ᵥ q)‖ ≤ C * nsq q := by
  have hcs := norm_star_dotProduct_sq_le q (A *ᵥ q)
  have h2 : ‖star q ⬝ᵥ (A *ᵥ q)‖ ^ 2 ≤ (C * nsq q) ^ 2 := by
    calc _ ≤ nsq q * nsq (A *ᵥ q) := hcs
      _ ≤ nsq q * (C ^ 2 * nsq q) := mul_le_mul_of_nonneg_left (hA q) (nsq_nonneg q)
      _ = (C * nsq q) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (nsq_nonneg q)) two_ne_zero).mp h2

end BlockBand.Palm.CoarseRelative
