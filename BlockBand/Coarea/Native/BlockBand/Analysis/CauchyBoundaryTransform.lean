module

public import BlockBand.Coarea.Native.BlockBand.Analysis.CauchyPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Cauchy boundary measure as angular measure

This file records the exact tangent change of variables which identifies the
standard Cauchy probability measure on the real line with normalized angular
measure on a semicircle.  It is the measure-theoretic bridge needed to turn a
disk mean-value formula into the upper-half-plane Poisson formula used in
the projected Wegner lemma.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Set

/-- Change variables by the tangent homeomorphism
`(-π/2, π/2) → ℝ`.  The statement is valid for arbitrary real-valued `f`;
Mathlib's integrals are totalized, and the Jacobian theorem supplies both
sides with the same value even outside the integrable case. -/
theorem integral_eq_integral_tan_jacobian (f : ℝ → ℝ) :
    (∫ t : ℝ, f t) =
      ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        (1 + Real.tan θ ^ 2) * f (Real.tan θ) := by
  have hderiv : ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivWithinAt Real.tan (1 / Real.cos θ ^ 2)
        (Ioo (-(Real.pi / 2)) (Real.pi / 2)) θ := by
    intro θ hθ
    exact (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo hθ).ne').hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv Real.injOn_tan f
  rw [Real.image_tan_Ioo] at h
  simp only [Measure.restrict_univ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  dsimp only
  rw [abs_of_pos (div_pos zero_lt_one (sq_pos_of_pos hcos))]
  simp only [smul_eq_mul]
  congr 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The standard Cauchy density is the pushforward of normalized Lebesgue
measure on `(-π/2, π/2)` under `tan`.  This is the exact normalization
`1 / (π(1+t²))` from the paper. -/
theorem integral_standardCauchyWeight_mul_eq_tan (f : ℝ → ℝ) :
    (∫ t : ℝ, standardCauchyWeight t * f t) =
      Real.pi⁻¹ *
        ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2), f (Real.tan θ) := by
  rw [integral_eq_integral_tan_jacobian]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    (∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        (1 + Real.tan θ ^ 2) *
          (standardCauchyWeight (Real.tan θ) * f (Real.tan θ))) =
      ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        Real.pi⁻¹ * f (Real.tan θ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ _hθ
          unfold standardCauchyWeight
          field_simp
    _ = Real.pi⁻¹ *
        ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2), f (Real.tan θ) := by
          rw [← integral_const_mul]

/-- Interval-integral form of `integral_standardCauchyWeight_mul_eq_tan`.
The endpoints have zero Lebesgue measure, so open and oriented interval
integrals agree. -/
theorem integral_standardCauchyWeight_mul_eq_tan_interval (f : ℝ → ℝ) :
    (∫ t : ℝ, standardCauchyWeight t * f t) =
      Real.pi⁻¹ *
        ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), f (Real.tan θ) := by
  rw [integral_standardCauchyWeight_mul_eq_tan]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- Full-circle parameterization of the standard Cauchy boundary measure.
The angle `φ` is sent to `tan (φ/2 - π/2)`; the exceptional endpoints are
Lebesgue-null.  This is the form directly compatible with Mathlib's
`Real.circleAverage`. -/
theorem integral_standardCauchyWeight_mul_eq_circleParam (f : ℝ → ℝ) :
    (∫ t : ℝ, standardCauchyWeight t * f t) =
      (2 * Real.pi)⁻¹ *
        ∫ φ in (0 : ℝ)..(2 * Real.pi),
          f (Real.tan (φ / 2 - Real.pi / 2)) := by
  rw [integral_standardCauchyWeight_mul_eq_tan_interval]
  have hsub := intervalIntegral.integral_comp_mul_sub
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (c := (1 / 2 : ℝ)) (fun θ : ℝ => f (Real.tan θ))
    (by norm_num) (Real.pi / 2)
  simp only [one_div, inv_inv] at hsub
  rw [show (2 : ℝ)⁻¹ * 0 - Real.pi / 2 = -(Real.pi / 2) by ring,
    show (2 : ℝ)⁻¹ * (2 * Real.pi) - Real.pi / 2 = Real.pi / 2 by ring]
    at hsub
  have hshape : (fun φ : ℝ => f (Real.tan (φ / 2 - Real.pi / 2))) =
      (fun φ : ℝ => f (Real.tan ((2 : ℝ)⁻¹ * φ - Real.pi / 2))) := by
    funext φ
    congr 2
    ring
  rw [hshape, hsub]
  field_simp [Real.pi_ne_zero]
  simp only [smul_eq_mul]

end CoareaNative.BlockBand
