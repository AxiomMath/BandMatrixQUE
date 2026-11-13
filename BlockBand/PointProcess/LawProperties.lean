module

public import BlockBand.PointProcess.Vague

/-!
# Intrinsic properties of marked point-process laws

Intensity and invariance are stated directly through compactly supported test
functions. This avoids opaque certificates and distinguishes counting
intensity from the mark-weighted spatial intensity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory

/-- Mean spectral counting measure is Lebesgue measure. -/
def HasUnitSpectralIntensity
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∀ f : CompactlySupportedContinuousMap ℝ ℝ,
    ∫ ξ, ∫ x, f x ∂ξ.spectral.measure
        ∂(law : Measure MarkedPointMeasure) = ∫ x, f x

/-- Mean mark-weighted intensity is `du dr`. This is distinct from the mean
counting measure on `ℝ × P(T)`. -/
def HasUniformSpatialIntensity
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∀ f : CompactlySupportedContinuousMap (ℝ × Torus) ℝ,
    ∫ ξ,
      ∫ z,
        (∫ r, f (z.1, r) ∂(z.2 : Measure Torus))
        ∂ξ.marked.measure
      ∂(law : Measure MarkedPointMeasure) =
    ∫ u : ℝ, ∫ r : Torus, f (u, r)

/-- Spectral stationarity, characterized by invariance of the marked Laplace
functional under every translation. -/
def IsSpectrallyStationary
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∀ (a : ℝ) (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ),
    (∀ z, 0 ≤ f z) →
    ∫ ξ, Real.exp (-∫ z, f (z.1 + a, z.2) ∂ξ.marked.measure)
        ∂(law : Measure MarkedPointMeasure) =
      ∫ ξ, Real.exp (-∫ z, f z ∂ξ.marked.measure)
        ∂(law : Measure MarkedPointMeasure)

/-- Simultaneous rotation invariance of all marks, again through the exact
Laplace functional. -/
def IsMarkRotationInvariant
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∀ (a : Torus) (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ),
    (∀ z, 0 ≤ f z) →
    ∫ ξ, Real.exp
        (-∫ z, f (z.1, z.2.map (Homeomorph.addLeft a))
          ∂ξ.marked.measure)
        ∂(law : Measure MarkedPointMeasure) =
      ∫ ξ, Real.exp (-∫ z, f z ∂ξ.marked.measure)
        ∂(law : Measure MarkedPointMeasure)

/-- Almost-sure simplicity of spectral locations. -/
def HasSimpleSpectralLocations
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∀ᵐ ξ ∂(law : Measure MarkedPointMeasure),
    IsSimplePointMeasure ξ.spectral

end BlockBand
