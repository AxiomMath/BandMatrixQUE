module

public import BlockBand.Model.Construction.SpectralRealization
public import BlockBand.Statements

/-!
# The finite physical realization and its marked law

A finite physical realization exists for every admissible parameter; its marked law is the
pushforward of the canonical physical Gaussian matrix law under the measurable marked
configuration map.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory ProbabilityTheory

/-- A finite physical realization for every admissible finite parameter. -/
def constructFiniteRealization (p : Parameters) : FiniteRealization p where
  model := p.constructGaussianRingModel
  spectral := constructSpectralRealization p p.constructGaussianRingModel

/-- Existence of a finite physical realization. -/
theorem nonempty_finiteRealization (p : Parameters) : Nonempty (FiniteRealization p) :=
  ⟨constructFiniteRealization p⟩

/-- The constructed marked law is exactly the measurable configuration pushforward
of the canonical raw physical Gaussian matrix law. -/
theorem constructFiniteRealization_markedLaw (p : Parameters) (E : ℝ) :
    ((constructFiniteRealization p).markedLaw E : Measure MarkedPointMeasure) =
      Measure.map (physicalOrderedMarkedConfig p E) (p.gaussianMatrixLaw : Measure p.SiteMatrix) := rfl

/-- Evaluation of the physical marked law on measurable sets. -/
theorem constructFiniteRealization_markedLaw_apply (p : Parameters) (E : ℝ)
    (A : Set MarkedPointMeasure) (hA : MeasurableSet A) :
    ((constructFiniteRealization p).markedLaw E : Measure MarkedPointMeasure) A =
      (p.gaussianMatrixLaw : Measure p.SiteMatrix) ((physicalOrderedMarkedConfig p E) ⁻¹' A) := by
  rw [constructFiniteRealization_markedLaw,
    Measure.map_apply (measurable_physicalOrderedMarkedConfig p E) hA]

/-- The marked random configuration has the constructed physical marked law. -/
theorem constructFiniteRealization_markedLaw_hasLaw (p : Parameters) (E : ℝ) :
    HasLaw (physicalOrderedMarkedConfig p E)
      ((constructFiniteRealization p).markedLaw E : Measure MarkedPointMeasure)
      (p.gaussianMatrixLaw : Measure p.SiteMatrix) :=
  ⟨(measurable_physicalOrderedMarkedConfig p E).aemeasurable,
    (constructFiniteRealization_markedLaw p E).symm⟩

end BlockBand.Model.Construction
