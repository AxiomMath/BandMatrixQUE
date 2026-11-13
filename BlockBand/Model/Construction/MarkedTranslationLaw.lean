module

public import BlockBand.Model.Construction.MarkedTranslation

/-!
# Global translation and weak convergence of marked laws

The pushforward of laws of marked point measures under the global translation is continuous in
the weak topology and preserves convergence of nets of laws.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Filter
open scoped Topology

/-- The pushforward of a law under the global marked translation. -/
def globalMarkedTranslationLaw (s : ℝ) (ν : ProbabilityMeasure MarkedPointMeasure) :
    ProbabilityMeasure MarkedPointMeasure := ν.map (globalMarkedTranslation s)

theorem globalMarkedTranslationLaw_measure (s : ℝ) (ν : ProbabilityMeasure MarkedPointMeasure) :
    (globalMarkedTranslationLaw s ν : Measure MarkedPointMeasure) =
      Measure.map (globalMarkedTranslation s) (ν : Measure MarkedPointMeasure) := rfl

theorem globalMarkedTranslationLaw_zero (ν : ProbabilityMeasure MarkedPointMeasure) :
    globalMarkedTranslationLaw 0 ν = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  have he : globalMarkedTranslation 0 = id := by
    funext ξ
    exact globalMarkedTranslation_zero ξ
  change Measure.map (globalMarkedTranslation 0) (ν : Measure MarkedPointMeasure) = _
  rw [he, Measure.map_id]

theorem globalMarkedTranslationLaw_add (s t : ℝ) (ν : ProbabilityMeasure MarkedPointMeasure) :
    globalMarkedTranslationLaw s (globalMarkedTranslationLaw t ν) =
      globalMarkedTranslationLaw (s+t) ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (globalMarkedTranslation s)
    (Measure.map (globalMarkedTranslation t) (ν : Measure MarkedPointMeasure)) =
      Measure.map (globalMarkedTranslation (s+t)) (ν : Measure MarkedPointMeasure)
  rw [Measure.map_map (measurable_globalMarkedTranslation s) (measurable_globalMarkedTranslation t)]
  congr 1
  funext ξ
  exact globalMarkedTranslation_add s t ξ

/-- A fixed translation of laws is continuous in the weak topology. -/
theorem continuous_globalMarkedTranslationLaw (s : ℝ) : Continuous (globalMarkedTranslationLaw s) :=
  ProbabilityMeasure.continuous_map (continuous_globalMarkedTranslation s)

/-- Every convergent net of marked laws translates to the translated limit;
no law-space uniqueness/separation theorem is needed for this implication. -/
theorem tendsto_globalMarkedTranslationLaw {J : Type*} {L : Filter J}
    (s : ℝ) (νs : J → ProbabilityMeasure MarkedPointMeasure)
    (ν : ProbabilityMeasure MarkedPointMeasure) (h : Tendsto νs L (𝓝 ν)) :
    Tendsto (fun j => globalMarkedTranslationLaw s (νs j)) L
      (𝓝 (globalMarkedTranslationLaw s ν)) :=
  (continuous_globalMarkedTranslationLaw s).continuousAt.tendsto.comp h

end BlockBand.Model.Construction
