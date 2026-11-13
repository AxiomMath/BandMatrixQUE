module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierStieltjesJointLaw
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Finite rectangular contour deformation

This module records the exact finite contour identity used in the APSSS shift.
It is a direct consequence of Mathlib's Cauchy–Goursat theorem; no limiting or
vertical-edge estimate is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory Set
open scoped Interval

/-- A holomorphic integrand may be moved from the real segment `[-R,R]` to the
parallel segment at height `-δ`; the two vertical edges are retained exactly. -/
theorem integral_real_segment_eq_shifted_add_vertical
    (f : ℂ → ℂ) (R δ : ℝ)
    (hf : DifferentiableOn ℂ f
      ([[(-R : ℂ) - δ * I |>.re, (R : ℂ).re]] ×ℂ
        [[((-R : ℂ) - δ * I).im, (R : ℂ).im]])) :
    (∫ x : ℝ in -R..R, f (x : ℂ)) =
      (∫ x : ℝ in -R..R, f ((x : ℂ) - δ * I)) +
        I * (∫ y : ℝ in -δ..0, f ((R : ℂ) + y * I)) -
        I * (∫ y : ℝ in -δ..0, f ((-R : ℂ) + y * I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((-R : ℂ) - δ * I) (R : ℂ) hf
  norm_num [Complex.mul_re, Complex.mul_im, smul_eq_mul] at h
  linear_combination -h

end PSSSNative.BlockBand.PSSS
