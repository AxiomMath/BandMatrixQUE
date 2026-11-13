module
public import BlockBand.Model.Construction.MarkedStateTopologyCountable
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Consequences of the marked state topology

Vague point measures on a locally compact second-countable Hausdorff space form a metrizable
Hausdorff space, the marked point measures are pseudometrizable, and laws of marked point
measures are determined by the expectations of bounded continuous functions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction

variable (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]

/-- Vague point measures are determined by their coordinates against compactly supported
continuous functions. -/
theorem vaguePointMeasure_coordinates_injective :
    Function.Injective (fun ξ : VaguePointMeasure X =>
      fun f : CompactlySupportedContinuousMap X ℝ => ξ.coordinate f) := by
  intro ξ η h
  apply vaguePointMeasure_eq_of_measure_eq
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact congrFun h f

theorem vaguePointMeasure_t2Space : T2Space (VaguePointMeasure X) := by
  have h : Topology.IsEmbedding (fun ξ : VaguePointMeasure X =>
      fun f : CompactlySupportedContinuousMap X ℝ => ξ.coordinate f) :=
    ⟨⟨rfl⟩, vaguePointMeasure_coordinates_injective X⟩
  exact h.t2Space

theorem vaguePointMeasure_metrizableSpace : MetrizableSpace (VaguePointMeasure X) := by
  have := vaguePointMeasure_pseudoMetrizableSpace X
  have := vaguePointMeasure_t2Space X
  infer_instance

/-- The vague point measures on the marked spectral space are pseudometrizable. -/
theorem markedVaguePointMeasure_pseudoMetrizableSpace :
    PseudoMetrizableSpace (VaguePointMeasure MarkedSpectralSpace) := by
  have := markedSpectralSpace_borelSpace
  exact vaguePointMeasure_pseudoMetrizableSpace MarkedSpectralSpace

theorem markedVaguePointMeasure_secondCountableTopology :
    SecondCountableTopology (VaguePointMeasure MarkedSpectralSpace) := by
  have := markedSpectralSpace_borelSpace
  exact vaguePointMeasure_secondCountableTopology MarkedSpectralSpace

theorem markedVaguePointMeasure_t2Space : T2Space (VaguePointMeasure MarkedSpectralSpace) := by
  have := markedSpectralSpace_borelSpace
  exact vaguePointMeasure_t2Space MarkedSpectralSpace

/-- The marked point measures are pseudometrizable, by their induced topology. -/
theorem markedPointMeasure_pseudoMetrizableSpace : PseudoMetrizableSpace MarkedPointMeasure := by
  have := markedVaguePointMeasure_pseudoMetrizableSpace
  exact (show Topology.IsInducing (fun ξ : MarkedPointMeasure => ξ.marked) from ⟨rfl⟩).pseudoMetrizableSpace

theorem markedPointMeasure_secondCountableTopology : SecondCountableTopology MarkedPointMeasure := by
  have := markedVaguePointMeasure_secondCountableTopology
  exact (show Topology.IsInducing (fun ξ : MarkedPointMeasure => ξ.marked) from ⟨rfl⟩).secondCountableTopology

theorem markedPointMeasure_t2Space : T2Space MarkedPointMeasure := by
  have := markedVaguePointMeasure_t2Space
  have h : Topology.IsEmbedding (fun ξ : MarkedPointMeasure => ξ.marked) := by
    refine ⟨⟨rfl⟩, ?_⟩
    intro ξ η h
    exact markedPointMeasure_eq_of_marked_measure_eq ξ η (congrArg VaguePointMeasure.measure h)
  exact h.t2Space

theorem markedPointMeasure_metrizableSpace : MetrizableSpace MarkedPointMeasure := by
  have := markedPointMeasure_pseudoMetrizableSpace
  have := markedPointMeasure_t2Space
  infer_instance

/-- Closed sets of marked point measures have outer approximations by continuous functions. -/
theorem markedPointMeasure_hasOuterApproxClosed : HasOuterApproxClosed MarkedPointMeasure := by
  have := markedPointMeasure_pseudoMetrizableSpace
  infer_instance

/-- The weak topology on laws of marked point measures is Hausdorff. -/
theorem markedPointMeasureLaw_t2Space : T2Space (ProbabilityMeasure MarkedPointMeasure) := by
  have := markedPointMeasure_hasOuterApproxClosed
  infer_instance

/-- Equality of all bounded continuous real expectations determines the law. -/
theorem markedPointMeasureLaw_eq_of_integrals (μ ν : ProbabilityMeasure MarkedPointMeasure)
    (h : ∀ f : MarkedPointMeasure →ᵇ ℝ,
      (∫ ξ, f ξ ∂(μ : Measure MarkedPointMeasure)) =
        ∫ ξ, f ξ ∂(ν : Measure MarkedPointMeasure)) : μ = ν := by
  have := markedPointMeasure_hasOuterApproxClosed
  have he : μ.toFiniteMeasure = ν.toFiniteMeasure := FiniteMeasure.ext_of_forall_integral_eq h
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg FiniteMeasure.toMeasure he

end BlockBand.Model.Construction
