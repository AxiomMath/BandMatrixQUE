module

public import BlockBand.Palm.OperatorProfile

/-!
# Quantitative covariance comparison

If `‖m - μ‖ ≤ ε Im μ` with `ε ≤ 1/4`, the zero-height covariance operators of a Hermitian `F` at
the parameters `m` and `μ` are comparable in the Loewner order within the factors `1 ∓ 4ε`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- If `‖b - a‖ ≤ ε‖a‖` with `ε ≤ 1/4`, then `|b|⁻²` is within the factors `1 ∓ 4ε` of
`|a|⁻²`. -/
theorem certificate_reciprocal_normSq_bounds
    {a b : ℂ} {ε : ℝ} (ha : a ≠ 0) (he : 0 ≤ ε) (he4 : ε ≤ 1 / 4)
    (hab : ‖b - a‖ ≤ ε * ‖a‖) :
    (1 - 4 * ε) / Complex.normSq a ≤ (Complex.normSq b)⁻¹ ∧
      (Complex.normSq b)⁻¹ ≤ (1 + 8 * ε) / Complex.normSq a := by
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hlo : (1 - ε) * ‖a‖ ≤ ‖b‖ := by
    have ht := norm_sub_norm_le a b
    rw [norm_sub_rev] at ht
    linarith
  have hhi : ‖b‖ ≤ (1 + ε) * ‖a‖ := by
    have ht := norm_sub_norm_le b a
    linarith
  have hB : 0 < ‖b‖ := by nlinarith
  have hloSq : (1 - ε) ^ 2 * ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have hp : 0 ≤ (1 - ε) * ‖a‖ := mul_nonneg (by linarith) (norm_nonneg _)
    nlinarith [sq_nonneg (‖b‖ - (1 - ε) * ‖a‖)]
  have hhiSq : ‖b‖ ^ 2 ≤ (1 + ε) ^ 2 * ‖a‖ ^ 2 := by
    have hp : 0 ≤ (1 + ε) * ‖a‖ := by positivity
    nlinarith [sq_nonneg ((1 + ε) * ‖a‖ - ‖b‖)]
  have heCube : 0 ≤ ε ^ 3 := by positivity
  have hpolyLo : (1 - 4 * ε) * (1 + ε) ^ 2 ≤ 1 := by nlinarith
  have heSq : ε ^ 2 ≤ ε / 4 := by nlinarith [mul_nonneg he (sub_nonneg.mpr he4)]
  have hpolyHi : 1 ≤ (1 + 8 * ε) * (1 - ε) ^ 2 := by nlinarith
  constructor
  · rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, inv_eq_one_div,
      div_le_div_iff₀ (sq_pos_of_pos hA) (sq_pos_of_pos hB)]
    have hx := mul_le_mul_of_nonneg_left hhiSq (by linarith : 0 ≤ 1 - 4 * ε)
    have hy := mul_le_mul_of_nonneg_right hpolyLo (sq_nonneg ‖a‖)
    nlinarith
  · rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, inv_eq_one_div,
      div_le_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hA)]
    have hx := mul_le_mul_of_nonneg_left hloSq (by positivity : 0 ≤ 1 + 8 * ε)
    have hy := mul_le_mul_of_nonneg_right hpolyHi (sq_nonneg ‖a‖)
    nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- A scalar perturbation small relative to Im μ preserves the upper half-plane. -/
theorem certificate_perturbed_im_pos {μ m : ℂ} {ε : ℝ}
    (hμ : 0 < μ.im) (he4 : ε ≤ 1 / 4) (hm : ‖m - μ‖ ≤ ε * μ.im) :
    0 < m.im := by
  have hi := Complex.abs_im_le_norm (m - μ)
  have hlo := (abs_le.mp (hi.trans hm)).1
  simp only [Complex.sub_im] at hlo
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Each spectral covariance entry has a uniform relative error, even at
arbitrarily large eigenvalues. -/
theorem certificate_covariance_entry_bounds
    (d E : ℝ) {c ε : ℝ} {μ m : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) (he : 0 ≤ ε) (he4 : ε ≤ 1 / 4)
    (hm : ‖m - μ‖ ≤ ε * μ.im) :
    (1 - 4 * ε) * zeroHeightProfileEntry c (c * μ.im) (d - E - c * μ.re) ≤
        zeroHeightProfileEntry c (c * m.im) (d - E - c * m.re) ∧
      zeroHeightProfileEntry c (c * m.im) (d - E - c * m.re) ≤
        (1 + 8 * ε) * zeroHeightProfileEntry c (c * μ.im) (d - E - c * μ.re) := by
  let a : ℂ := (d : ℂ) - ((E : ℂ) + c * μ)
  let b : ℂ := (d : ℂ) - ((E : ℂ) + c * m)
  have ha : a ≠ 0 := by
    intro hzero
    have hi := congrArg Complex.im hzero
    simp [a] at hi
    rcases hi with hi | hi
    · exact hc.ne' hi
    · exact hμ.ne' hi
  have hnorma : c * μ.im ≤ ‖a‖ := by
    have hi := Complex.abs_im_le_norm a
    simpa [a, abs_of_pos (mul_pos hc hμ)] using hi
  have hba : b - a = -(c : ℂ) * (m - μ) := by dsimp [a, b]; ring
  have hab : ‖b - a‖ ≤ ε * ‖a‖ := by
    rw [hba, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖m - μ‖ ≤ c * (ε * μ.im) := mul_le_mul_of_nonneg_left hm hc.le
      _ = ε * (c * μ.im) := by ring
      _ ≤ ε * ‖a‖ := mul_le_mul_of_nonneg_left hnorma he
  have h := certificate_reciprocal_normSq_bounds ha he he4 hab
  have haSq : Complex.normSq a = (d - E - c * μ.re) ^ 2 + (c * μ.im) ^ 2 := by
    simp [a, Complex.normSq_apply]
    ring
  have hbSq : Complex.normSq b = (d - E - c * m.re) ^ 2 + (c * m.im) ^ 2 := by
    simp [b, Complex.normSq_apply]
    ring
  rw [haSq, hbSq] at h
  unfold zeroHeightProfileEntry
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 hc.le
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left h.2 hc.le
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm] using hh

/-- A nonnegative diagonal matrix in the eigenbasis of `F` is positive semidefinite. -/
theorem certificate_spectral_posSemidef
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (profileSpectralAut F hF (Matrix.diagonal (fun i => (d i : ℂ)))).PosSemidef := by
  unfold profileSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr (hd i)

/-- Lower Loewner comparison of the zero-height covariance operators at `m` and `μ`. -/
theorem certificate_covariance_lower
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E ε : ℝ} {μ m : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) (he : 0 ≤ ε) (he4 : ε ≤ 1 / 4)
    (hm : ‖m - μ‖ ≤ ε * μ.im) :
    (zeroHeightOperator F E c m.re m.im -
      ((1 - 4 * ε : ℝ) : ℂ) • zeroHeightOperator F E c μ.re μ.im).PosSemidef := by
  have hmp := certificate_perturbed_im_pos hμ he4 hm
  rw [zeroHeightOperator_eq_spectral F hF hc hmp,
    zeroHeightOperator_eq_spectral F hF hc hμ, ← map_smul, ← map_sub]
  have hdiag : Matrix.diagonal (fun i =>
      (zeroHeightProfileEntry c (c * m.im) (hF.eigenvalues i - E - c * m.re) : ℂ)) -
      ((1 - 4 * ε : ℝ) : ℂ) • Matrix.diagonal (fun i =>
        (zeroHeightProfileEntry c (c * μ.im) (hF.eigenvalues i - E - c * μ.re) : ℂ)) =
      Matrix.diagonal (fun i => ((zeroHeightProfileEntry c (c * m.im)
        (hF.eigenvalues i - E - c * m.re) - (1 - 4 * ε) *
          zeroHeightProfileEntry c (c * μ.im)
            (hF.eigenvalues i - E - c * μ.re) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag]
  apply certificate_spectral_posSemidef
  intro i
  exact sub_nonneg.mpr (certificate_covariance_entry_bounds
    (hF.eigenvalues i) E hc hμ he he4 hm).1

/-- Upper Loewner comparison of the zero-height covariance operators at `m` and `μ`. -/
theorem certificate_covariance_upper
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E ε : ℝ} {μ m : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) (he : 0 ≤ ε) (he4 : ε ≤ 1 / 4)
    (hm : ‖m - μ‖ ≤ ε * μ.im) :
    (((1 + 8 * ε : ℝ) : ℂ) • zeroHeightOperator F E c μ.re μ.im -
      zeroHeightOperator F E c m.re m.im).PosSemidef := by
  have hmp := certificate_perturbed_im_pos hμ he4 hm
  rw [zeroHeightOperator_eq_spectral F hF hc hμ,
    zeroHeightOperator_eq_spectral F hF hc hmp, ← map_smul, ← map_sub]
  have hdiag : ((1 + 8 * ε : ℝ) : ℂ) • Matrix.diagonal (fun i =>
      (zeroHeightProfileEntry c (c * μ.im) (hF.eigenvalues i - E - c * μ.re) : ℂ)) -
      Matrix.diagonal (fun i =>
        (zeroHeightProfileEntry c (c * m.im) (hF.eigenvalues i - E - c * m.re) : ℂ)) =
      Matrix.diagonal (fun i => (((1 + 8 * ε) *
        zeroHeightProfileEntry c (c * μ.im) (hF.eigenvalues i - E - c * μ.re) -
          zeroHeightProfileEntry c (c * m.im)
            (hF.eigenvalues i - E - c * m.re) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag]
  apply certificate_spectral_posSemidef
  intro i
  exact sub_nonneg.mpr (certificate_covariance_entry_bounds
    (hF.eigenvalues i) E hc hμ he he4 hm).2

end BlockBand.Palm
