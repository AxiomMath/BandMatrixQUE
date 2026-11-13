module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The APSSS Gaussian quadratic-ratio analytic core

This module records the unconditional pieces of the Fourier/contour argument in
Aizenman–Peled–Schenker–Shamis–Sodin, Lemma 2.1 and Section 6.  In
particular, every declaration below is a theorem about Mathlib's
integrals; there is no analytic-input structure.

Source normalization: a real standard Gaussian has density
`(2π)⁻¹/² exp (-x²/2)`.  The complex powers in the closed formula use Lean's
principal `Complex.cpow`.  The half-plane hypothesis on the quadratic
coefficient is kept explicit, exactly as required during the finite contour
deformation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory
open scoped ComplexConjugate ENNReal Interval

/-- The complex quadratic exponent appearing after multiplying a standard
Gaussian density by the characteristic phase of a shifted square.

For APSSS (6.12), use `q = I * w - 1 / 2`, `c = 2 * I * w * β`, and
`d = I * w * β^2`. -/
def gaussianSquareExponent (q c d : ℂ) (x : ℝ) : ℂ :=
  q * (x : ℂ) ^ 2 + c * (x : ℂ) + d

/-- Gaussian-square characteristic transform in its branch-stable quadratic
form.  This is Mathlib's principal-square-root Gaussian integral, exposed with
the APSSS normalization variables. -/
theorem integral_exp_gaussianSquareExponent {q : ℂ} (hq : q.re < 0) (c d : ℂ) :
    ∫ x : ℝ, Complex.exp (gaussianSquareExponent q c d x) =
      ((Real.pi : ℂ) / -q) ^ (1 / 2 : ℂ) *
        Complex.exp (d - c ^ 2 / (4 * q)) := by
  simpa only [gaussianSquareExponent] using integral_cexp_quadratic hq c d

/-- APSSS's analytic coefficient `1 - 2 i w`. -/
def gaussianSquareDenominator (w : ℂ) : ℂ := 1 - 2 * I * w

/-- On the continuation half-plane the analytic coefficient cannot vanish. -/
theorem gaussianSquareDenominator_ne_zero {w : ℂ}
    (hw : 0 < (gaussianSquareDenominator w).re) :
    gaussianSquareDenominator w ≠ 0 := by
  intro h
  rw [h] at hw
  simp at hw

/-- Closed principal-branch factor for one shifted Gaussian square.  Products
of these factors are the continued characteristic transform in APSSS
(6.13)--(6.16). -/
def gaussianSquareTransform (w : ℂ) (β : ℝ) : ℂ :=
  (gaussianSquareDenominator w) ^ (-(1 / 2 : ℂ)) *
    Complex.exp
      (I * w / gaussianSquareDenominator w * (β : ℂ) ^ 2)

/-- APSSS's coefficient energy `E_j²(1+b_j²)`. -/
def coefficientEnergy {n : ℕ} (E b : Fin n → ℝ) (j : Fin n) : ℝ :=
  E j ^ 2 * (1 + b j ^ 2)

/-- Every coefficient energy is nonnegative. -/
theorem coefficientEnergy_nonneg {n : ℕ} (E b : Fin n → ℝ) (j : Fin n) :
    0 ≤ coefficientEnergy E b j := by
  exact mul_nonneg (sq_nonneg _) (by positivity)

/-- The tail energy after the first `r` dominant coordinates. -/
def tailEnergy {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ j : Fin n, if r ≤ (j : ℕ) then coefficientEnergy E b j else 0

/-- Tail energy is nonnegative, which is the sign fact needed for APSSS's
choice `δ = 1/(10ν²)`. -/
theorem tailEnergy_nonneg {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) :
    0 ≤ tailEnergy E b r := by
  unfold tailEnergy
  exact Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact coefficientEnergy_nonneg E b j
    · exact le_rfl

end PSSSNative.BlockBand.PSSS
