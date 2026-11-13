module
public import BlockBand.Counting.OpenIntervalEvaluation
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Spectral projection of marked configurations

The projection from marked configurations to their spectral point measures is continuous
in the vague topology, since compactly supported tests on the spectral line pull back to
compactly supported tests on the marked space.  Hence open-interval two-point events are
open on marked configurations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

/-- Pullback along `Prod.fst` retains compact support because the mark space is compact. -/
def spectralProjectionTestPullback (f : CompactlySupportedContinuousMap ℝ ℝ) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun := fun z => f z.1
  continuous_toFun := f.continuous.comp continuous_fst
  hasCompactSupport' := by
    apply (f.hasCompactSupport.prod (isCompact_univ : IsCompact (univ : Set MassProfile))).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal
    · intro z hz
      exact ⟨subset_tsupport f hz, mem_univ _⟩
    · exact (isClosed_tsupport f).prod isClosed_univ

/-- The spectral pushforward has exactly the pulled-back marked coordinate. -/
theorem spectralProjection_coordinate (ξ : MarkedPointMeasure)
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ξ.spectral.coordinate f = ξ.marked.coordinate (spectralProjectionTestPullback f) := by
  unfold VaguePointMeasure.coordinate
  rw [ξ.spectral_eq]
  exact integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable

/-- Spectral projection is continuous in the marked vague topology. -/
theorem continuous_markedSpectralProjection : Continuous MarkedPointMeasure.spectralProjection := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  have hc : Continuous (fun ξ : MarkedPointMeasure => ξ.marked) := continuous_induced_dom
  change Continuous (fun ξ : MarkedPointMeasure => ξ.spectral.coordinate f)
  simp_rw [spectralProjection_coordinate]
  exact (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate _).comp hc

/-- Every open-interval spectral mass superlevel event is open on marked configurations. -/
theorem isOpen_marked_Ioo_mass_gt (a b : ℝ) (r : ℝ≥0∞) :
    IsOpen {ξ : MarkedPointMeasure | r < ξ.spectral.measure (Ioo a b)} :=
  (isOpen_vague_Ioo_mass_gt a b r).preimage continuous_markedSpectralProjection

end BlockBand.Counting
