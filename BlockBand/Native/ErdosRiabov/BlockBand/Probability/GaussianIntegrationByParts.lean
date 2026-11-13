module

public import BlockBand.Native.ErdosRiabov.BlockBand.Conventions
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian integration by parts

This module proves the one-coordinate Gaussian integration-by-parts formula.  The variance parameter
is Mathlib's `NNReal`
variance, not a standard deviation.  The hypotheses are a strong `C¹`
version: the test and its displayed derivative
are required to have exactly the Gaussian-weighted integrability needed by
whole-line integration by parts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand

open MeasureTheory ProbabilityTheory

/-- The derivative of the centered real Gaussian density of positive variance.
This is the scalar density calculation behind Gaussian integration by parts. -/
theorem hasDerivAt_centeredGaussianPDFReal
    (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v)
      (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hfun :
      (fun y : ℝ => -(y - 0) ^ 2 / (2 * (v : ℝ))) =
      fun y : ℝ => -(2 * (v : ℝ))⁻¹ * y ^ 2 := by
    funext y
    field_simp
    ring
  have hq : HasDerivAt
      (fun y : ℝ => -(y - 0) ^ 2 / (2 * (v : ℝ)))
      (-(x / (v : ℝ))) x := by
    rw [hfun]
    convert ((hasDerivAt_id x).pow 2).const_mul (-(2 * (v : ℝ))⁻¹) using 1
    · funext y
      simp only [Pi.pow_apply, id_eq]
    · simp only [id_eq, Nat.cast_ofNat]
      field_simp
      ring
  have hpdf := hq.exp.const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  rw [gaussianPDFReal_def]
  convert hpdf using 1; ring

/-- Real centered Gaussian integration by parts, in density form.  This statement uses a
complex-valued test because that is the form needed for resolvent entries. -/
theorem realGaussianIntegrationByParts_density
    (v : NNReal) (hv : v ≠ 0) (f f' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hxf : Integrable (fun x =>
      ((x * gaussianPDFReal 0 v x : ℝ) : ℂ) * f x))
    (hdf : Integrable (fun x =>
      ((gaussianPDFReal 0 v x : ℝ) : ℂ) * f' x))
    (hf : Integrable (fun x =>
      ((gaussianPDFReal 0 v x : ℝ) : ℂ) * f x)) :
    (∫ x : ℝ, ((x : ℂ) * f x) ∂gaussianReal 0 v) =
      (v : ℝ) * ∫ x : ℝ, f' x ∂gaussianReal 0 v := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => f x)
    (v := fun x : ℝ => (gaussianPDFReal 0 v x : ℂ))
    (u' := f')
    (v' := fun x : ℝ =>
      ((-(x / (v : ℝ)) * gaussianPDFReal 0 v x : ℝ) : ℂ))
    (fun x _ => hderiv x)
    (fun x _ => (hasDerivAt_centeredGaussianPDFReal v hv x).ofReal_comp)
  have hleft : Integrable
      ((fun x : ℝ => f x) * fun x : ℝ =>
        ((-(x / (v : ℝ)) * gaussianPDFReal 0 v x : ℝ) : ℂ)) := by
    convert hxf.const_mul (-(v : ℝ)⁻¹ : ℂ) using 1
    funext x
    dsimp
    push_cast
    field_simp
  have hright : Integrable
      (f' * fun x : ℝ => (gaussianPDFReal 0 v x : ℂ)) := by
    convert hdf using 1
    funext x
    simp [mul_comm]
  have hprod : Integrable
      ((fun x : ℝ => f x) * fun x : ℝ =>
        (gaussianPDFReal 0 v x : ℂ)) := by
    convert hf using 1
    funext x
    simp [mul_comm]
  specialize hibp hleft hright hprod
  rw [integral_gaussianReal_eq_integral_smul hv,
      integral_gaussianReal_eq_integral_smul hv]
  change
    (∫ x : ℝ, ((gaussianPDFReal 0 v x : ℝ) : ℂ) *
      ((x : ℂ) * f x)) =
      ((v : ℝ) : ℂ) *
        ∫ x : ℝ, ((gaussianPDFReal 0 v x : ℝ) : ℂ) * f' x
  have hscale :
      (∫ x : ℝ,
        f x * ((-(x / (v : ℝ)) * gaussianPDFReal 0 v x : ℝ) : ℂ)) =
      (-(v : ℝ)⁻¹ : ℂ) *
        ∫ x : ℝ, ((x * gaussianPDFReal 0 v x : ℝ) : ℂ) * f x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    field_simp
  rw [hscale] at hibp
  have hleftIntegral :
      (∫ x : ℝ, ((gaussianPDFReal 0 v x : ℝ) : ℂ) *
        ((x : ℂ) * f x)) =
      ∫ x : ℝ, ((x * gaussianPDFReal 0 v x : ℝ) : ℂ) * f x := by
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    ring
  rw [hleftIntegral]
  have hrightIntegral :
      (∫ x : ℝ, ((gaussianPDFReal 0 v x : ℝ) : ℂ) * f' x) =
      ∫ x : ℝ, f' x * (gaussianPDFReal 0 v x : ℝ) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hrightIntegral]
  let I : ℂ := ∫ x : ℝ,
    ((x * gaussianPDFReal 0 v x : ℝ) : ℂ) * f x
  let J : ℂ := ∫ x : ℝ, f' x * (gaussianPDFReal 0 v x : ℝ)
  change I = ((v : ℝ) : ℂ) * J
  change (-(v : ℝ)⁻¹ : ℂ) * I = -J at hibp
  calc
    I = (-((v : ℝ) : ℂ)) * ((-(v : ℝ)⁻¹ : ℂ) * I) := by
      rw [← mul_assoc]
      have hc : (-((v : ℝ) : ℂ)) * (-(v : ℝ)⁻¹ : ℂ) = 1 := by
        rw [neg_mul_neg, ← Complex.ofReal_mul]
        simp [hvR]
      rw [hc, one_mul]
    _ = (-((v : ℝ) : ℂ)) * (-J) := by rw [hibp]
    _ = ((v : ℝ) : ℂ) * J := by ring

/-- The circular complex Gaussian law of variance `t`, represented by the
independent real and imaginary coordinates of variance `t/2`.  We keep the
coordinate space as `ℝ × ℝ`; the map `(x,y) ↦ x+iy` is used explicitly in the
integration formulas below. -/
def circularGaussianMeasure (t : NNReal) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (t / 2)).prod (gaussianReal 0 (t / 2))

end ERNative.BlockBand
