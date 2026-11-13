module

public import BlockBand.Native.CEH.BlockBand.Conventions
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian integration by parts

This module proves the one-coordinate Gaussian integration-by-parts formula.  The variance parameter is Mathlib's `NNReal`
variance, not a standard deviation.  The hypotheses are the strong `C¹`
version used by the formal development: the test and its displayed derivative
are required to have exactly the Gaussian-weighted integrability needed by
whole-line integration by parts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand

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

/-- Real centered Gaussian integration by parts, in density form.  The source
is the Gaussian integration-by-parts identity; this statement uses a
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

/-- Circular Gaussian integration by parts in split real coordinates.  A
circular variable of variance `t` is written `Z = X + iY`, where `X,Y` are
centered real Gaussians of variance `t/2`.  The mixed order of the iterated
integrals makes both one-dimensional integrations by parts explicit.  When
the corresponding product functions are integrable, the next theorem applies
Fubini and identifies these expressions with the circular Gaussian law.

The two conclusions are precisely
`E[Z f] = t E[(∂ₓ + i∂ᵧ)f/2]` and
`E[conj Z f] = t E[(∂ₓ - i∂ᵧ)f/2]`, the conventions of
the Gaussian integration-by-parts identity. -/
theorem circularGaussianIntegrationByParts
    (t : NNReal) (ht : t ≠ 0)
    (f fx fy : ℝ → ℝ → ℂ)
    (hderivX : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hderivY : ∀ x y, HasDerivAt (fun u => f x u) (fy x y) y)
    (hxCoord : ∀ y, Integrable (fun x =>
      ((x * gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * f x y))
    (hxDeriv : ∀ y, Integrable (fun x =>
      ((gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * fx x y))
    (hxTest : ∀ y, Integrable (fun x =>
      ((gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * f x y))
    (hyCoord : ∀ x, Integrable (fun y =>
      ((y * gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * f x y))
    (hyDeriv : ∀ x, Integrable (fun y =>
      ((gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * fy x y))
    (hyTest : ∀ x, Integrable (fun y =>
      ((gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * f x y)) :
    let γ := gaussianReal 0 (t / 2)
    ((∫ y, (∫ x, (x : ℂ) * f x y ∂γ) ∂γ) +
        Complex.I * (∫ x, (∫ y, (y : ℂ) * f x y ∂γ) ∂γ) =
      (t : ℝ) *
        (((∫ y, (∫ x, fx x y ∂γ) ∂γ) +
          Complex.I * (∫ x, (∫ y, fy x y ∂γ) ∂γ)) / 2)) ∧
    ((∫ y, (∫ x, (x : ℂ) * f x y ∂γ) ∂γ) -
        Complex.I * (∫ x, (∫ y, (y : ℂ) * f x y ∂γ) ∂γ) =
      (t : ℝ) *
        (((∫ y, (∫ x, fx x y ∂γ) ∂γ) -
          Complex.I * (∫ x, (∫ y, fy x y ∂γ) ∂γ)) / 2)) := by
  dsimp only
  have hw : t / 2 ≠ 0 := div_ne_zero ht (by norm_num)
  have hX (y : ℝ) := realGaussianIntegrationByParts_density
    (t / 2) hw (fun x => f x y) (fun x => fx x y)
    (fun x => hderivX x y) (hxCoord y) (hxDeriv y) (hxTest y)
  have hY (x : ℝ) := realGaussianIntegrationByParts_density
    (t / 2) hw (fun y => f x y) (fun y => fy x y)
    (fun y => hderivY x y) (hyCoord x) (hyDeriv x) (hyTest x)
  have hXi :
      (∫ y, (∫ x, (x : ℂ) * f x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2)) =
      ((t / 2 : NNReal) : ℝ) *
        ∫ y, (∫ x, fx x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2) := by
    calc
      _ = ∫ y, ((t / 2 : NNReal) : ℝ) *
          (∫ x, fx x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2) := by
            apply integral_congr_ae
            filter_upwards with y
            exact hX y
      _ = _ := by rw [integral_const_mul]
  have hYi :
      (∫ x, (∫ y, (y : ℂ) * f x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2)) =
      ((t / 2 : NNReal) : ℝ) *
        ∫ x, (∫ y, fy x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2) := by
    calc
      _ = ∫ x, ((t / 2 : NNReal) : ℝ) *
          (∫ y, fy x y ∂gaussianReal 0 (t / 2))
          ∂gaussianReal 0 (t / 2) := by
            apply integral_congr_ae
            filter_upwards with x
            exact hY x
      _ = _ := by rw [integral_const_mul]
  constructor <;> rw [hXi, hYi]
  · push_cast
    ring
  · push_cast
    ring

/-- The circular complex Gaussian law of variance `t`, represented by the
independent real and imaginary coordinates of variance `t/2`.  We keep the
coordinate space as `ℝ × ℝ`; the map `(x,y) ↦ x+iy` is used explicitly in the
integration formulas below. -/
def circularGaussianMeasure (t : NNReal) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (t / 2)).prod (gaussianReal 0 (t / 2))

/-- Product-measure form of circular Gaussian integration by parts.  Unlike
`circularGaussianIntegrationByParts`, this theorem is stated as an
expectation against the circular product law; its four product-integrability
hypotheses are precisely those needed for Fubini and linearity of the Bochner
integral. -/
theorem circularGaussianIntegrationByParts_product
    (t : NNReal) (ht : t ≠ 0)
    (f fx fy : ℝ → ℝ → ℂ)
    (hderivX : ∀ x y, HasDerivAt (fun u => f u y) (fx x y) x)
    (hderivY : ∀ x y, HasDerivAt (fun u => f x u) (fy x y) y)
    (hxCoord : ∀ y, Integrable (fun x =>
      ((x * gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * f x y))
    (hxDeriv : ∀ y, Integrable (fun x =>
      ((gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * fx x y))
    (hxTest : ∀ y, Integrable (fun x =>
      ((gaussianPDFReal 0 (t / 2) x : ℝ) : ℂ) * f x y))
    (hyCoord : ∀ x, Integrable (fun y =>
      ((y * gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * f x y))
    (hyDeriv : ∀ x, Integrable (fun y =>
      ((gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * fy x y))
    (hyTest : ∀ x, Integrable (fun y =>
      ((gaussianPDFReal 0 (t / 2) y : ℝ) : ℂ) * f x y))
    (hxf : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * f p.1 p.2)
      (circularGaussianMeasure t))
    (hyf : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) * f p.1 p.2)
      (circularGaussianMeasure t))
    (hfx : Integrable (fun p : ℝ × ℝ => fx p.1 p.2)
      (circularGaussianMeasure t))
    (hfy : Integrable (fun p : ℝ × ℝ => fy p.1 p.2)
      (circularGaussianMeasure t)) :
    ((∫ p : ℝ × ℝ,
        ((p.1 : ℂ) + Complex.I * p.2) * f p.1 p.2
        ∂circularGaussianMeasure t) =
      (t : ℝ) * ∫ p : ℝ × ℝ,
        (fx p.1 p.2 + Complex.I * fy p.1 p.2) / 2
        ∂circularGaussianMeasure t) ∧
    ((∫ p : ℝ × ℝ,
        ((p.1 : ℂ) - Complex.I * p.2) * f p.1 p.2
        ∂circularGaussianMeasure t) =
      (t : ℝ) * ∫ p : ℝ × ℝ,
        (fx p.1 p.2 - Complex.I * fy p.1 p.2) / 2
        ∂circularGaussianMeasure t) := by
  have hsplit := circularGaussianIntegrationByParts t ht f fx fy
    hderivX hderivY hxCoord hxDeriv hxTest hyCoord hyDeriv hyTest
  let γ := gaussianReal 0 (t / 2)
  have hXprod :
      (∫ p : ℝ × ℝ, (p.1 : ℂ) * f p.1 p.2
        ∂circularGaussianMeasure t) =
      ∫ y, (∫ x, (x : ℂ) * f x y ∂γ) ∂γ := by
    exact integral_prod_symm _ hxf
  have hYprod :
      (∫ p : ℝ × ℝ, (p.2 : ℂ) * f p.1 p.2
        ∂circularGaussianMeasure t) =
      ∫ x, (∫ y, (y : ℂ) * f x y ∂γ) ∂γ := by
    exact integral_prod _ hyf
  have hFXprod :
      (∫ p : ℝ × ℝ, fx p.1 p.2 ∂circularGaussianMeasure t) =
      ∫ y, (∫ x, fx x y ∂γ) ∂γ := by
    exact integral_prod_symm _ hfx
  have hFYprod :
      (∫ p : ℝ × ℝ, fy p.1 p.2 ∂circularGaussianMeasure t) =
      ∫ x, (∫ y, fy x y ∂γ) ∂γ := by
    exact integral_prod _ hfy
  have hIY : Integrable
      (fun p : ℝ × ℝ => Complex.I * ((p.2 : ℂ) * f p.1 p.2))
      (circularGaussianMeasure t) := hyf.const_mul _
  have hIFY : Integrable
      (fun p : ℝ × ℝ => Complex.I * fy p.1 p.2)
      (circularGaussianMeasure t) := hfy.const_mul _
  constructor
  · rw [show (fun p : ℝ × ℝ =>
          ((p.1 : ℂ) + Complex.I * p.2) * f p.1 p.2) =
        (fun p => (p.1 : ℂ) * f p.1 p.2 +
          Complex.I * ((p.2 : ℂ) * f p.1 p.2)) by
          funext p; ring]
    rw [integral_add hxf hIY, integral_const_mul, hXprod, hYprod]
    rw [integral_div, integral_add hfx hIFY, integral_const_mul,
      hFXprod, hFYprod]
    exact hsplit.1
  · rw [show (fun p : ℝ × ℝ =>
          ((p.1 : ℂ) - Complex.I * p.2) * f p.1 p.2) =
        (fun p => (p.1 : ℂ) * f p.1 p.2 -
          Complex.I * ((p.2 : ℂ) * f p.1 p.2)) by
          funext p; ring]
    rw [integral_sub hxf hIY, integral_const_mul, hXprod, hYprod]
    rw [integral_div, integral_sub hfx hIFY, integral_const_mul,
      hFXprod, hFYprod]
    exact hsplit.2

end CEHNative.BlockBand
