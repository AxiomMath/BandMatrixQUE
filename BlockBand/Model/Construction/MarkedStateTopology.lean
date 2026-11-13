module
public import BlockBand.Model.Construction.MarkedTranslation
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Topology and Borel structure of mass profiles

The space `MassProfile` of probability measures on the torus is compact, metrizable and second
countable, and its Giry σ-algebra coincides with the Borel σ-algebra of the weak topology.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set TopologicalSpace Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

theorem massProfile_compactSpace : CompactSpace MassProfile := inferInstance

theorem massProfile_metrizableSpace : MetrizableSpace MassProfile := inferInstance

theorem massProfile_secondCountableTopology : SecondCountableTopology MassProfile := inferInstance

/-- A second-countable initial coordinate topology has measurable opens when
all its coordinates are measurable. The coordinate index need not be countable. -/
theorem opensMeasurableSpace_of_initial_pi {S I : Type*} [MeasurableSpace S]
    [TopologicalSpace S] [SecondCountableTopology S] (c : S → I → ℝ≥0)
    (hc : ∀ i, Measurable (fun x => c x i))
    (ht : (inferInstance : TopologicalSpace S) =
      TopologicalSpace.induced c Pi.topologicalSpace) : OpensMeasurableSpace S := by
  constructor
  let b : Set (Set (I → ℝ≥0)) :=
    {g | ∃ (s : I → Set ℝ≥0) (i : Finset I), (∀ a ∈ i, IsOpen (s a)) ∧ g = Set.pi (↑i) s}
  have ht' : (inferInstance : TopologicalSpace S) =
      TopologicalSpace.generateFrom (Set.preimage c '' b) := by
    rw [ht, pi_eq_generateFrom, induced_generateFrom_eq]
  rw [borel_eq_generateFrom_of_subbasis ht']
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨g, ⟨s, i, hi, rfl⟩, rfl⟩
  have he : c ⁻¹' Set.pi (↑i) s = ⋂ a ∈ i, (fun x => c x a) ⁻¹' s a := by
    ext x
    simp
  rw [he]
  exact MeasurableSet.biInter i.countable_toSet (fun a ha => (hi a ha).measurableSet.preimage (hc a))

theorem measurable_massProfile_testAgainstNN (f : Torus →ᵇ ℝ≥0) :
    Measurable (fun μ : MassProfile => μ.toFiniteMeasure.testAgainstNN f) := by
  change Measurable (fun μ : MassProfile => (∫⁻ x, f x ∂(μ : Measure Torus)).toNNReal)
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_lintegral (ENNReal.continuous_coe.comp f.continuous).measurable).comp
      measurable_subtype_coe)

/-- The Giry σ-algebra contains the opens of the weak topology. -/
theorem massProfile_opensMeasurableSpace : OpensMeasurableSpace MassProfile := by
  apply opensMeasurableSpace_of_initial_pi
    (fun μ : MassProfile => fun f : Torus →ᵇ ℝ≥0 => μ.toFiniteMeasure.testAgainstNN f)
    measurable_massProfile_testAgainstNN
  change TopologicalSpace.induced ProbabilityMeasure.toFiniteMeasure
    (TopologicalSpace.induced FiniteMeasure.toWeakDualBCNN
      (TopologicalSpace.induced (fun φ f => φ f) Pi.topologicalSpace)) = _
  rw [induced_compose, induced_compose]
  rfl

/-- Evaluation on every open Torus set is lower semicontinuous in the weak topology. -/
theorem lowerSemicontinuous_massProfile_apply_open (G : Set Torus) (hG : IsOpen G) :
    LowerSemicontinuous (fun μ : MassProfile => (μ : Measure Torus) G) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro μ
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (continuous_id.tendsto μ : Tendsto (fun ν : MassProfile => ν) (𝓝 μ) (𝓝 μ)) hG

/-- Giry evaluation of every Torus Borel set is measurable for the weak Borel algebra. -/
theorem massProfile_borel_measurable_toMeasure :
    @Measurable MassProfile (Measure Torus) (borel MassProfile) inferInstance
      (fun μ => (μ : Measure Torus)) := by
  let : MeasurableSpace MassProfile := borel MassProfile
  let : BorelSpace MassProfile := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq.trans rfl : (inferInstance : MeasurableSpace Torus) = MeasurableSpace.generateFrom {G | IsOpen G}) isPiSystem_isOpen
  intro G hG
  exact (lowerSemicontinuous_massProfile_apply_open G hG).measurable

/-- The Giry σ-algebra on `MassProfile` is the Borel σ-algebra of the weak topology. -/
theorem massProfile_borelSpace : BorelSpace MassProfile := by
  constructor
  apply le_antisymm
  · have hm := massProfile_borel_measurable_toMeasure
    have hid : @Measurable MassProfile MassProfile (borel MassProfile) inferInstance id :=
      Measurable.subtype_mk hm
    intro A hA
    simpa only [Set.preimage_id] using hid hA
  · exact massProfile_opensMeasurableSpace.borel_le

theorem massProfile_hasOuterApproxClosed : HasOuterApproxClosed MassProfile := inferInstance

theorem markedSpectralSpace_metrizableSpace : MetrizableSpace MarkedSpectralSpace := inferInstance

theorem markedSpectralSpace_secondCountableTopology : SecondCountableTopology MarkedSpectralSpace := inferInstance

theorem markedSpectralSpace_locallyCompactSpace : LocallyCompactSpace MarkedSpectralSpace := inferInstance

theorem markedSpectralSpace_borelSpace : BorelSpace MarkedSpectralSpace := by
  have : BorelSpace MassProfile := massProfile_borelSpace
  infer_instance

end BlockBand.Model.Construction
