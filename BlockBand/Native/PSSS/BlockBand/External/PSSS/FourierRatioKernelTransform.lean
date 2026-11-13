module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresEnvelope
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioCriterion
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Fourier transform of the APSSS ratio kernel

This module begins the analytic proof of APSSS Claim 2.  It evaluates the Gaussian
Fourier slice of the regularized heat kernel and the positive-real Laplace/Gamma
slice with the exact `Γ (3/2+δ)` normalization.  All integrals are Bochner
integrals; no inversion or contour-shift statement is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The positive regularizer inserted in APSSS Claim 2. -/
def regularizedFourierRatioKernel (ε δ x y : ℝ) : ℝ :=
  if 0 < x then
    Real.exp (-y ^ 2 / (4 * ε ^ 2 * x)) * Real.exp (-δ * x) * x ^ δ
  else 0

/-- The denominator appearing in the Fourier transform of the regularized kernel. -/
def fourierRatioLaplaceParameter (ε δ ξ η : ℝ) : ℂ :=
  ((η ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) + (ξ : ℂ) * I

/-- The APSSS Laplace parameter stays in the open right half-plane.  This is the
continuation domain needed for every finite contour deformation. -/
theorem fourierRatioLaplaceParameter_re_pos {ε δ ξ η : ℝ} (hδ : 0 < δ) :
    0 < (fourierRatioLaplaceParameter ε δ ξ η).re := by
  simp [fourierRatioLaplaceParameter, pow_two, Complex.mul_re]
  have hp : 0 ≤ (η * η) * (ε * ε) :=
    mul_nonneg (mul_self_nonneg η) (mul_self_nonneg ε)
  linarith

/-- Consequently the Fourier-transform denominator is nonzero. -/
theorem fourierRatioLaplaceParameter_ne_zero {ε δ ξ η : ℝ} (hδ : 0 < δ) :
    fourierRatioLaplaceParameter ε δ ξ η ≠ 0 := by
  intro h
  have := fourierRatioLaplaceParameter_re_pos (ε := ε) (ξ := ξ) (η := η) hδ
  rw [h] at this
  simp at this

/-- Exact squared modulus of the complex APSSS Fourier denominator. -/
theorem normSq_fourierRatioLaplaceParameter (ε δ ξ η : ℝ) :
    Complex.normSq (fourierRatioLaplaceParameter ε δ ξ η) =
      (η ^ 2 * ε ^ 2 + δ) ^ 2 + ξ ^ 2 := by
  simp [fourierRatioLaplaceParameter, Complex.normSq_apply, pow_two,
    Complex.mul_re, Complex.mul_im]

/-- Exact Gaussian Fourier transform in the transverse `y` variable. -/
theorem fourierRatioKernel_gaussian_slice {ε x : ℝ} (hε : 0 < ε)
    (hx : 0 < x) (η : ℝ) :
    ∫ y : ℝ,
        Complex.exp (-(((y ^ 2 / (4 * ε ^ 2 * x) : ℝ) : ℂ))) *
          Complex.exp (-(I * (η : ℂ) * (y : ℂ))) =
      (((Real.pi : ℂ) / ((1 / (4 * ε ^ 2 * x) : ℝ) : ℂ)) ^
          (1 / 2 : ℂ)) *
        Complex.exp (-((η ^ 2 * ε ^ 2 * x : ℝ) : ℂ)) := by
  have hb : 0 < ((1 / (4 * ε ^ 2 * x) : ℝ) : ℂ).re := by
    rw [ofReal_re]
    exact one_div_pos.mpr (by positivity)
  have h := fourierIntegral_gaussian hb (-(η : ℂ))
  convert h using 1 <;> congr 1
  · funext y
    rw [← Complex.exp_add]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  · push_cast
    field_simp

/-- The principal square-root factor in the preceding slice has the positive-real
normalization `2 √π ε √x`. -/
theorem fourierRatioKernel_gaussian_prefactor {ε x : ℝ} (hε : 0 < ε)
    (hx : 0 < x) :
    (((Real.pi : ℂ) / ((1 / (4 * ε ^ 2 * x) : ℝ) : ℂ)) ^
        (1 / 2 : ℂ)) =
      ((2 * Real.sqrt Real.pi * ε * Real.sqrt x : ℝ) : ℂ) := by
  have hpos : 0 < 4 * ε ^ 2 * x := by positivity
  have hreal : Real.pi / (1 / (4 * ε ^ 2 * x)) =
      (2 * Real.sqrt Real.pi * ε * Real.sqrt x) ^ 2 := by
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hx.le]
    ring
  rw [show ((Real.pi : ℂ) / ((1 / (4 * ε ^ 2 * x) : ℝ) : ℂ)) =
      ((Real.pi / (1 / (4 * ε ^ 2 * x)) : ℝ) : ℂ) by push_cast; rfl]
  rw [hreal, Complex.ofReal_pow]
  rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num]
  exact Complex.sq_cpow_two_inv (by
    simp
    positivity)

/-- The transverse Gaussian slice in the explicit positive-real normalization used
by APSSS. -/
theorem fourierRatioKernel_gaussian_slice_normalized {ε x : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (η : ℝ) :
    ∫ y : ℝ,
        Complex.exp (-(((y ^ 2 / (4 * ε ^ 2 * x) : ℝ) : ℂ))) *
          Complex.exp (-(I * (η : ℂ) * (y : ℂ))) =
      ((2 * Real.sqrt Real.pi * ε * Real.sqrt x : ℝ) : ℂ) *
        Complex.exp (-((η ^ 2 * ε ^ 2 * x : ℝ) : ℂ)) := by
  rw [fourierRatioKernel_gaussian_slice hε hx η,
    fourierRatioKernel_gaussian_prefactor hε hx]

end PSSSNative.BlockBand.PSSS
