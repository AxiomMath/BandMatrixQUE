module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioCriterion

/-!
# Modulus bounds for the shifted APSSS characteristic function

This module isolates the continuation/modulus computation in APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), (6.17)--(6.23).
The variable `d` is the downward contour displacement multiplied by `Eⱼ²`, and
`ζ` is the real affine Fourier frequency.  All powers remain Mathlib's principal
powers; their norms reduce to real powers because the exponent `-1/2` is real.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory
open scoped ENNReal NNReal

/-- A shifted real Fourier frequency `ζ - i d`. -/
def shiftedSquareFrequency (ζ d : ℝ) : ℂ := (ζ : ℂ) - d * I

/-- Its Gaussian-square denominator has the APSSS Cartesian form
`(1-2d)-2iζ`. -/
theorem gaussianSquareDenominator_shifted (ζ d : ℝ) :
    gaussianSquareDenominator (shiftedSquareFrequency ζ d) =
      ((1 - 2 * d : ℝ) : ℂ) - 2 * ζ * I := by
  simp [gaussianSquareDenominator, shiftedSquareFrequency]
  ring_nf
  simp
  ring

/-- Squared modulus of the continued denominator, APSSS (6.17). -/
theorem normSq_gaussianSquareDenominator_shifted (ζ d : ℝ) :
    Complex.normSq (gaussianSquareDenominator (shiftedSquareFrequency ζ d)) =
      (1 - 2 * d) ^ 2 + 4 * ζ ^ 2 := by
  rw [gaussianSquareDenominator_shifted]
  simp [Complex.normSq_apply]
  ring

/-- Real part of the shifted exponential exponent in the one-coordinate transform. -/
theorem re_shiftedSquare_exponent (ζ d b : ℝ) :
    (I * shiftedSquareFrequency ζ d /
      gaussianSquareDenominator (shiftedSquareFrequency ζ d) * (b : ℂ) ^ 2).re =
      b ^ 2 * (d * (1 - 2 * d) - 2 * ζ ^ 2) /
        ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) := by
  rw [gaussianSquareDenominator_shifted]
  rw [show (b : ℂ) ^ 2 = ((b ^ 2 : ℝ) : ℂ) by norm_cast]
  rw [mul_re]
  simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
  simp [shiftedSquareFrequency, Complex.mul_re, Complex.div_re,
    Complex.normSq_apply]
  field_simp
  ring

/-- Exact modulus of one continued shifted-square factor.  This is APSSS (6.17)
with the square-root factor written canonically as a real power of the complex norm. -/
theorem gaussianSquareTransform_shifted_norm {ζ d : ℝ}
    (b : ℝ) :
    ‖gaussianSquareTransform (shiftedSquareFrequency ζ d) b‖ =
      ‖gaussianSquareDenominator (shiftedSquareFrequency ζ d)‖ ^ (-(1 / 2 : ℝ)) *
        Real.exp
          (b ^ 2 * (d * (1 - 2 * d) - 2 * ζ ^ 2) /
            ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2)) := by
  unfold gaussianSquareTransform
  rw [norm_mul]
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_real, Complex.norm_exp]
  rw [re_shiftedSquare_exponent]

/-- APSSS's affine tail frequency `ζⱼ = ξ Eⱼ² + η Eⱼ`. -/
def tailAffineFrequency (E : ℝ) (ξ η : ℝ) : ℝ := ξ * E ^ 2 + η * E

/-- The continued frequency used after shifting `ξ` down by `δ`. -/
theorem weightedSquareFrequency_shift_eq {n : ℕ} (E : Fin n → ℝ)
    (r : ℕ) (ξ η δ : ℝ) (j : Fin n) (hj : r ≤ (j : ℕ)) :
    weightedSquareFrequency E r ((ξ : ℂ) - δ * I) (η : ℂ) j =
      shiftedSquareFrequency (tailAffineFrequency (E j) ξ η) (δ * E j ^ 2) := by
  simp [weightedSquareFrequency, shiftedSquareFrequency, tailAffineFrequency,
    show ¬(j : ℕ) < r by omega]
  ring

/-- On a dominant coordinate (`j<r`) the contour shift does not enter. -/
theorem weightedSquareFrequency_shift_eq_dominant {n : ℕ} (E : Fin n → ℝ)
    (r : ℕ) (ξ η δ : ℝ) (j : Fin n) (hj : (j : ℕ) < r) :
    weightedSquareFrequency E r ((ξ : ℂ) - δ * I) (η : ℂ) j =
      (η * E j : ℝ) := by
  simp [weightedSquareFrequency, hj]

/-- A single tail coefficient energy is bounded by the total tail energy. -/
theorem coefficientEnergy_le_tailEnergy {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (j : Fin n) (hj : r ≤ (j : ℕ)) :
    coefficientEnergy E b j ≤ tailEnergy E b r := by
  unfold tailEnergy
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n =>
      if r ≤ (i : ℕ) then coefficientEnergy E b i else 0)
    (fun i _ => by
      split_ifs
      · exact coefficientEnergy_nonneg E b i
      · exact le_rfl)
    (Finset.mem_univ j)
  simpa [hj] using h

end PSSSNative.BlockBand.PSSS
