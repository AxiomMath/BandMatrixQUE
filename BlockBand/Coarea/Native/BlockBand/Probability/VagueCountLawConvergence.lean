module

public import BlockBand.Coarea.Native.BlockBand.Counting.BoundaryRegularLimitLaw
public import BlockBand.Coarea.Native.BlockBand.Probability.IntegerCountExponentialPortmanteau
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence of boundary-regular local count laws

This module supplies the continuous-mapping step for
`BoundaryRegularLimitLawInput`.  It proves the almost-everywhere continuous mapping
theorem for weakly convergent probability measures, then applies it to local
restriction masses in `VagueRationalWindowState`.  Thus the scalar field
`mass_laws_tendsto` follows from ambient weak convergence and the
paper's null-boundary condition.

The result does not manufacture the separate exponential-uniform-integrability
fields in `PaperCountingWeakExponentialUIInput`: those remain quantitative
finite-volume inputs.  Nor does it identify an externally supplied
`ProbabilityMeasure ℕ` count law with the `NNReal` pushforward used here; such
an identification is a separate hypothesis.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u v w

/-- The closure of the preimage of a closed set can acquire new points only
where `f` is discontinuous.  This is the topological core of the a.e.-continuous
mapping theorem. -/
theorem closure_preimage_subset_preimage_union_not_continuousAt
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) {F : Set Y} (hF : IsClosed F) :
    closure (f ⁻¹' F) ⊆
      f ⁻¹' F ∪ {x | ¬ ContinuousAt f x} := by
  intro x hx
  by_cases hcont : ContinuousAt f x
  · left
    have himage : f x ∈ closure (f '' (f ⁻¹' F)) := mem_closure_image hcont hx
    have hsub : f '' (f ⁻¹' F) ⊆ F := by
      rintro y ⟨z, hz, rfl⟩
      exact hz
    exact hF.closure_eq ▸ closure_mono hsub himage
  · exact Or.inr hcont

/-- **Almost-everywhere continuous mapping theorem.**  Along a countably
 generated filter, weak convergence of probability measures is preserved by a
 measurable map which is continuous almost everywhere for the limiting law.

This is the Portmanteau argument used implicitly in the paper: for a
closed target set, close its preimage; the extra closure points lie in the
null discontinuity set. -/
theorem ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuousAt
    {X : Type u} {Y : Type v} {ι : Type w}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    [OpensMeasurableSpace Y]
    {L : Filter ι} [L.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    {f : X → Y}
    (hμ : Tendsto μs L (𝓝 μ))
    (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun i => (μs i).map f) L (𝓝 (μ.map f)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have hmap (ρ : ProbabilityMeasure X) :
      ((ρ.map f : ProbabilityMeasure Y) : Measure Y) F =
        (ρ : Measure X) (f ⁻¹' F) := by
    exact Measure.map_apply hf hF.measurableSet
  simp_rw [hmap]
  calc
    limsup (fun i => (μs i : Measure X) (f ⁻¹' F)) L ≤
        limsup (fun i => (μs i : Measure X) (closure (f ⁻¹' F))) L :=
      limsup_le_limsup (.of_forall fun i =>
        measure_mono subset_closure)
    _ ≤ (μ : Measure X) (closure (f ⁻¹' F)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ ≤ (μ : Measure X)
        (f ⁻¹' F ∪ {x | ¬ ContinuousAt f x}) :=
      measure_mono
        (closure_preimage_subset_preimage_union_not_continuousAt f hF)
    _ ≤ (μ : Measure X) (f ⁻¹' F) +
        (μ : Measure X) {x | ¬ ContinuousAt f x} := measure_union_le _ _
    _ = (μ : Measure X) (f ⁻¹' F) := by
      have hnull : (μ : Measure X) {x | ¬ ContinuousAt f x} = 0 := by
        rw [← ae_iff]
        simpa only [Set.mem_ofPred_eq, not_not] using hcont
      rw [hnull, add_zero]

/-- Boundary regularity of one local determining set supplies the exact a.e.
continuity hypothesis needed by the general mapping theorem. -/
theorem tendsto_localRestrictionMassLaw_of_ambient_of_null_frontier
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {κ : Type u} {α : Type v} {L : Filter α} [L.IsCountablyGenerated]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (hμ : Tendsto μs L (𝓝 μ)) (n : ℕ) (k : κ)
    (hboundary :
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        (ν n : Measure (MarkedSpectralSpace Unit))
          (frontier (sets n k)) = 0) :
    Tendsto (fun i => localRestrictionMassLaw (μs i) sets n k) L
      (𝓝 (localRestrictionMassLaw μ sets n k)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuousAt hμ
    (measurable_localRestrictionMass sets hsets n k)
  filter_upwards [hboundary] with ν hν
  exact continuousAt_localRestrictionMass_of_null_frontier sets n k ν hν

/-- Construct the scalar-law part of `NaturalRestrictionLawClosureInput`.
The only new hypothesis is the limit null-frontier condition; ambient weak convergence and
finite-volume natural-valuedness do the rest. -/
theorem naturalRestrictionLawClosureInputOfAmbient
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {κ : Type u} {α : Type v} {L : Filter α} [L.IsCountablyGenerated]
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (hμ : Tendsto μs L (𝓝 μ))
    (hboundary : ∀ n k,
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        (ν n : Measure (MarkedSpectralSpace Unit))
          (frontier (sets n k)) = 0)
    (hnatural : ∀ i,
      ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
        HasNaturalLocalRestrictionMass sets ν) :
    NaturalRestrictionLawClosureInput L μs μ sets where
  sets_measurable := hsets
  ambient_law_tendsto := hμ
  mass_laws_tendsto := fun n k =>
    tendsto_localRestrictionMassLaw_of_ambient_of_null_frontier
      sets hsets hμ n k (hboundary n k)
  approximants_natural := hnatural

/-- A boundary-regular translated rational family therefore needs no separate
scalar weak-convergence assumption. -/
theorem shiftedRationalNaturalRestrictionLawClosureInputOfAmbient
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type v} {L : Filter α} [L.IsCountablyGenerated]
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (s : ℝ) (hμ : Tendsto μs L (𝓝 μ))
    (hboundary : ∀ n q,
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        (ν n : Measure (MarkedSpectralSpace Unit))
          (frontier (shiftedRationalDeterminingFamily s n q)) = 0)
    (hnatural : ∀ i,
      ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
        HasNaturalLocalRestrictionMass
          (shiftedRationalDeterminingFamily s) ν) :
    NaturalRestrictionLawClosureInput L μs μ
      (shiftedRationalDeterminingFamily s) :=
  naturalRestrictionLawClosureInputOfAmbient μs μ
    (shiftedRationalDeterminingFamily s)
    (fun n q => measurableSet_shiftedRationalDeterminingFamily s n q)
    hμ hboundary hnatural

/-- Assemble `BoundaryRegularLimitLawInput` with every scalar restriction-law
convergence field proved by the a.e.-continuous mapping theorem.  What remains
explicit is exactly boundary regularity for each translated rational family
and natural-valuedness of the finite configurations. -/
def boundaryRegularLimitLawInputOfAmbient
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type v} {L : Filter α} [L.IsCountablyGenerated]
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (consistency : ConsistentLimitLawClosureInput L μs μ)
    (hboundary : ∀ s n q,
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        (ν n : Measure (MarkedSpectralSpace Unit))
          (frontier (shiftedRationalDeterminingFamily s n q)) = 0)
    (hnatural : ∀ s i,
      ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
        HasNaturalLocalRestrictionMass
          (shiftedRationalDeterminingFamily s) ν) :
    BoundaryRegularLimitLawInput L μs μ where
  consistency := consistency
  natural := fun s =>
    shiftedRationalNaturalRestrictionLawClosureInputOfAmbient μs μ s
      consistency.ambient_law_tendsto (hboundary s) (hnatural s)

end CoareaNative.BlockBand
