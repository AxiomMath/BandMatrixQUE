module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.APSSSQuadraticRatio

/-!
# Gaussian-square characteristic transforms

Concrete one-dimensional and finite-product identities used in APSSS (6.12)--(6.16).
The continuation domain is the half-plane where `1 - 2 i w` has positive real part,
and every complex power is Mathlib's principal `Complex.cpow`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- APSSS (6.12), including its analytic continuation: the characteristic transform of
a shifted square of one standard real Gaussian, on the principal branch. -/
theorem integral_exp_mul_sq_gaussian_complex (w : ℂ)
    (hw : 0 < (gaussianSquareDenominator w).re) (β : ℝ) :
    ∫ h : ℝ, Complex.exp (I * w * ((h + β : ℝ) : ℂ) ^ 2)
        ∂gaussianReal 0 1 = gaussianSquareTransform w β := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero ]
  -- expose the single complex quadratic Gaussian integral
  have hq : (I * w - (1 / 2 : ℂ)).re < 0 := by
    have := hw
    simp [gaussianSquareDenominator] at this ⊢
    linarith
  rw [show (fun h : ℝ =>
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(h ^ 2) / 2)) •
          Complex.exp (I * w * ((h + β : ℝ) : ℂ) ^ 2)) =
      (fun h : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ •
          Complex.exp (gaussianSquareExponent (I * w - 1 / 2)
            (2 * I * w * β) (I * w * β ^ 2) h)) by
      funext h
      simp only [mul_smul, Complex.real_smul, Complex.ofReal_exp,
        gaussianSquareExponent]
      rw [← Complex.exp_add]
      push_cast
      ring_nf]
  rw [integral_smul, integral_exp_gaussianSquareExponent hq]
  let D : ℂ := gaussianSquareDenominator w
  have hDre : 0 < D.re := hw
  have hD : D ≠ 0 := gaussianSquareDenominator_ne_zero hw
  have hqD : -(I * w - (1 / 2 : ℂ)) = D / 2 := by
    dsimp [D, gaussianSquareDenominator]
    ring
  have hq0 : I * w - (1 / 2 : ℂ) ≠ 0 := by
    intro h
    apply hD
    dsimp [D, gaussianSquareDenominator]
    linear_combination -2 * h
  have hqexpr : I * w - (1 / 2 : ℂ) = -D / 2 := by
    linear_combination -hqD
  have hexp :
      I * w * (β : ℂ) ^ 2 - (2 * I * w * β) ^ 2 /
          (4 * (I * w - 1 / 2)) =
        I * w / D * (β : ℂ) ^ 2 := by
    rw [hqexpr]
    field_simp [hD]
    dsimp [D, gaussianSquareDenominator]
    ring
  rw [hexp, hqD]
  unfold gaussianSquareTransform
  change (Real.sqrt (2 * Real.pi))⁻¹ •
      (((Real.pi : ℂ) / (D / 2)) ^ (1 / 2 : ℂ) *
        Complex.exp (I * w / D * (β : ℂ) ^ 2)) =
    D ^ (-(1 / 2 : ℂ)) * Complex.exp (I * w / D * (β : ℂ) ^ 2)
  rw [Complex.real_smul]
  have hnorm :
      (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ *
          (((Real.pi : ℂ) / (D / 2)) ^ (1 / 2 : ℂ)) =
        D ^ (-(1 / 2 : ℂ)) := by
    -- Principal-branch normalization:
    -- `(2π)⁻¹/² · (2π D⁻¹)¹/² = D⁻¹/²` on `re D > 0`.
    rw [show (Real.pi : ℂ) / (D / 2) =
        (((2 * Real.pi : ℝ) : ℂ) * D⁻¹) by
      field_simp [hD]
      push_cast
      ring]
    have harg : D.arg ≠ Real.pi :=
      Complex.slitPlane_arg_ne_pi (Complex.mem_slitPlane_iff.mpr (Or.inl hDre))
    rw [Complex.cpow_neg]
    rw [← Complex.inv_cpow D (1 / 2 : ℂ) harg]
    have hr : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hlog : Complex.log (((2 * Real.pi : ℝ) : ℂ) * D⁻¹) =
        (Real.log (2 * Real.pi) : ℂ) + Complex.log D⁻¹ :=
      Complex.log_ofReal_mul hr (inv_ne_zero hD)
    have hsqrt : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) =
        (((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
      rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num]
      change ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) =
        Complex.sqrt ((2 * Real.pi : ℝ) : ℂ)
      symm
      rw [Complex.sqrt_of_nonneg]
      · simp
      · exact_mod_cast hr.le
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr hr.ne') (inv_ne_zero hD))]
    rw [hlog, add_mul, Complex.exp_add]
    rw [Complex.ofReal_log hr.le]
    rw [← Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]
    rw [← Complex.cpow_def_of_ne_zero (inv_ne_zero hD)]
    rw [← hsqrt]
    field_simp [Real.sqrt_ne_zero'.mpr hr]
  push_cast
  rw [← mul_assoc, hnorm]

/-- The frequency attached to the `j`th independent Gaussian square in the APSSS
dominant-coordinate split.  The first `r` coordinates carry the linear Fourier
frequency `η Eⱼ`; the remaining coordinates also carry the quadratic-ratio frequency
`ξ Eⱼ²`. -/
def weightedSquareFrequency {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (ξ η : ℂ) (j : Fin n) : ℂ :=
  if (j : ℕ) < r then η * E j else ξ * E j ^ 2 + η * E j

/-- The characteristic transform of finitely many independent shifted Gaussian
squares factors into the product of the one-dimensional principal-branch transforms.
The measure is the finite product of standard real Gaussian measures. -/
theorem integral_exp_sum_mul_sq_gaussian {n : ℕ} (w : Fin n → ℂ)
    (β : Fin n → ℝ)
    (hw : ∀ j, 0 < (gaussianSquareDenominator (w j)).re) :
    ∫ g : Fin n → ℝ,
        Complex.exp (∑ j, I * w j * ((g j + β j : ℝ) : ℂ) ^ 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      ∏ j, gaussianSquareTransform (w j) (β j) := by
  rw [show (fun g : Fin n → ℝ =>
      Complex.exp (∑ j, I * w j * ((g j + β j : ℝ) : ℂ) ^ 2)) =
      (fun g : Fin n → ℝ =>
        ∏ j, Complex.exp (I * w j * ((g j + β j : ℝ) : ℂ) ^ 2)) by
    funext g
    exact Complex.exp_sum Finset.univ
      (fun j => I * w j * ((g j + β j : ℝ) : ℂ) ^ 2)]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun (j : Fin n) (h : ℝ) =>
      Complex.exp (I * w j * ((h + β j : ℝ) : ℂ) ^ 2))]
  apply Finset.prod_congr rfl
  intro j _
  exact integral_exp_mul_sq_gaussian_complex (w j) (hw j) (β j)

/-- APSSS specialization of finite Gaussian-square factorization to the dominant
coordinate frequencies `weightedSquareFrequency`. -/
theorem integral_exp_weightedSquares_pi {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ξ η : ℂ)
    (hhalf : ∀ j, 0 <
      (gaussianSquareDenominator (weightedSquareFrequency E r ξ η j)).re) :
    ∫ g : Fin n → ℝ,
        Complex.exp
          (∑ j, I * weightedSquareFrequency E r ξ η j *
            ((g j + b j : ℝ) : ℂ) ^ 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      ∏ j, gaussianSquareTransform
        (weightedSquareFrequency E r ξ η j) (b j) :=
  integral_exp_sum_mul_sq_gaussian
    (fun j => weightedSquareFrequency E r ξ η j) b hhalf

/-- For real Fourier frequencies every weighted-square denominator lies on the
vertical line with real part one, hence automatically belongs to the continuation
half-plane. -/
theorem weightedSquareDenominator_re_real {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (ξ η : ℝ) (j : Fin n) :
    (gaussianSquareDenominator
      (weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j)).re = 1 := by
  have hfreq :
      weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j =
        ((if (j : ℕ) < r then η * E j else ξ * E j ^ 2 + η * E j : ℝ) : ℂ) := by
    simp only [weightedSquareFrequency]
    split_ifs <;> push_cast <;> ring
  rw [hfreq]
  simp [gaussianSquareDenominator]

/-- The unconditional real-frequency characteristic-function factorization for the
finite family of independent weighted Gaussian squares. -/
theorem integral_exp_weightedSquares_pi_real {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ξ η : ℝ) :
    ∫ g : Fin n → ℝ,
        Complex.exp
          (∑ j, I * weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j *
            ((g j + b j : ℝ) : ℂ) ^ 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      ∏ j, gaussianSquareTransform
        (weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j) (b j) := by
  apply integral_exp_weightedSquares_pi
  intro j
  rw [weightedSquareDenominator_re_real]
  norm_num

end PSSSNative.BlockBand.PSSS
