module

public import BlockBand.Model.Parameters

/-!
# The physical complex-Hermitian Gaussian block-band law

The physical Gaussian block-band model with row-variance-one normalization. The joint
characteristic function is used as the definition of the law: this simultaneously fixes
centredness, all real component variances, independence, and the absence of entries outside the
cyclic nearest-neighbour band.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Parameters

/-- Matrices indexed by the physical sites. -/
abbrev SiteMatrix (p : Parameters) := Matrix p.Site p.Site ℂ

/-- Canonical row-major index of a physical site. -/
def siteIndex (p : Parameters) (x : p.Site) : ℕ :=
  x.1.val * p.W + x.2.val

/-- The variance profile `E |H_xy|²`. -/
def entryVariance (p : Parameters) (x y : p.Site) : ℝ :=
  if y.1 = x.1 then p.c / p.W
  else if y.1 = x.1 + 1 ∨ y.1 = x.1 - 1 then p.b / p.W
  else 0

/-- The exact real-linear coordinate pairing used in the characteristic
function. Diagonal coefficients multiply real diagonal entries, while each
strict upper-triangular complex entry contributes independent real and
imaginary coordinates. -/
def coordinatePairing (p : Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
  (H : p.SiteMatrix) : ℝ :=
  (∑ x, d x * (H x x).re) +
    ∑ x, ∑ y with p.siteIndex x < p.siteIndex y,
      (u x y * (H x y).re + v x y * (H x y).im)

/-- Quadratic form of the physical Gaussian coordinates. Off-diagonal real
and imaginary components each have half the total complex variance. -/
def coordinateVariance (p : Parameters)
  (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) : ℝ :=
  (∑ x, p.entryVariance x x * (d x) ^ 2) +
    ∑ x, ∑ y with p.siteIndex x < p.siteIndex y,
      (p.entryVariance x y / 2) * ((u x y) ^ 2 + (v x y) ^ 2)

/-- A probability law is exactly the physical Gaussian block-band ring law
when it is supported on Hermitian matrices and has the displayed joint
characteristic function, including all independence and normalization clauses. -/
def IsPhysicalGaussianRingLaw (p : Parameters)
    (law : ProbabilityMeasure p.SiteMatrix) : Prop :=
  (∀ᵐ H ∂(law : Measure p.SiteMatrix), H.IsHermitian) ∧
  ∀ (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ),
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂(law : Measure p.SiteMatrix) =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2)

/-- A realization of the exact finite physical model. It contains no analytic
or asymptotic conclusion. -/
structure GaussianRingModel (p : Parameters) where
  law : ProbabilityMeasure p.SiteMatrix
  isPhysical : p.IsPhysicalGaussianRingLaw law

/-- Auxiliary normalization in which the diagonal GUE coefficient is one.
Headline observables never use this matrix implicitly. -/
def normalizedMatrix (p : Parameters) (H : p.SiteMatrix) : p.SiteMatrix :=
  ((Real.sqrt p.c : ℂ)⁻¹) • H

theorem normalizedMatrix_apply (p : Parameters) (H : p.SiteMatrix) (x y : p.Site) :
    p.normalizedMatrix H x y = (Real.sqrt p.c : ℂ)⁻¹ * H x y := by
  rfl

end Parameters

end BlockBand
