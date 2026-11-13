module

public import BlockBand.Coarea.Native.BlockBand.Counting.BoundaryAvoidingEndpoints
public import BlockBand.Coarea.Native.BlockBand.Counting.MarkedProcessTightness

/-!
# Law-level closure at boundary-regular vague limits

This module upgrades the samplewise closure statements to probability laws.
For each local determining set, its restriction mass is a measurable
`NNReal`-valued observable.  If the laws of these observables converge and the
approximating laws are supported on natural-valued masses, Portmanteau and the
closedness of the natural casts imply the same almost-sure support statement
for the limit law.

The scalar-law convergence is kept explicit.  It is the precise
continuous-mapping consequence justified by null frontiers; Mathlib does not
currently provide the general almost-everywhere-continuous mapping theorem
needed to derive it directly from weak convergence of the ambient laws.

Projective consistency is treated by an equally explicit closed carrier.  The
carrier must contain every approximating law and must imply consistency at
boundary-regular points.  This avoids the false claim that sharp restriction
is globally continuous on the whole finite-measure space.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u v

/-- The total mass of one local restriction, as an `NNReal`-valued observable
on the ambient weak-product state. -/
def localRestrictionMass
    {κ : Type u}
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (n : ℕ) (k : κ) (ν : VagueRationalWindowState) : NNReal :=
  ((ν n).restrict (sets n k)).mass

/-- On a measurable determining set, restriction mass is ordinary finite
measure evaluation. -/
theorem localRestrictionMass_eq_apply
    {κ : Type u}
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (n : ℕ) (k : κ) (ν : VagueRationalWindowState) :
    localRestrictionMass sets n k ν = (ν n) (sets n k) := by
  exact FiniteMeasure.restrict_mass (ν n) (sets n k)

/-- Restriction mass is measurable for every Borel determining set. -/
theorem measurable_localRestrictionMass
    {κ : Type u}
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (n : ℕ) (k : κ) :
    Measurable (localRestrictionMass sets n k) := by
  rw [show localRestrictionMass sets n k =
      fun ν => (ν n) (sets n k) by
    funext ν
    exact localRestrictionMass_eq_apply sets n k ν]
  change Measurable (fun ν : VagueRationalWindowState =>
    ENNReal.toNNReal
      ((ν n : Measure (MarkedSpectralSpace Unit)) (sets n k)))
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_coe (hsets n k)).comp
      (measurable_subtype_coe.comp (measurable_pi_apply n)))

/-- At a measure which does not charge the frontier, the local restriction
mass observable is continuous.  This is the pointwise continuous-mapping
input behind the law-level interface below. -/
theorem continuousAt_localRestrictionMass_of_null_frontier
    {κ : Type u}
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (n : ℕ) (k : κ) (ν : VagueRationalWindowState)
    (hboundary :
      (ν n : Measure (MarkedSpectralSpace Unit))
        (frontier (sets n k)) = 0) :
    ContinuousAt (localRestrictionMass sets n k) ν := by
  have hcoord :
      Tendsto (fun ρ : VagueRationalWindowState => ρ n)
        (𝓝 ν) (𝓝 (ν n)) :=
    (continuous_apply n).continuousAt
  have hboundary' :
      (ν n) (frontier (sets n k)) = 0 := by
    apply ENNReal.coe_injective
    simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ENNReal.coe_zero] using hboundary
  have happly := FiniteMeasure.tendsto_apply_of_null_frontier
    hcoord hboundary'
  rw [show localRestrictionMass sets n k =
      fun ρ => (ρ n) (sets n k) by
    funext ρ
    exact localRestrictionMass_eq_apply sets n k ρ]
  exact happly

/-- The pushforward law of one local restriction mass. -/
def localRestrictionMassLaw
    {κ : Type u}
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (n : ℕ) (k : κ) : ProbabilityMeasure NNReal :=
  μ.map (localRestrictionMass sets n k)

/-- Exact scalar continuous-mapping data for a family of local restrictions.
The first field is the ambient weak convergence.  The second records
its required scalar consequence, while the third records natural-valued
approximating counts. -/
structure NaturalRestrictionLawClosureInput
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} {α : Type v} (L : Filter α)
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit)) : Prop where
  sets_measurable : ∀ n k, MeasurableSet (sets n k)
  ambient_law_tendsto : Tendsto μs L (𝓝 μ)
  mass_laws_tendsto :
    ∀ n k, Tendsto
      (fun i => localRestrictionMassLaw (μs i) sets n k) L
      (𝓝 (localRestrictionMassLaw μ sets n k))
  approximants_natural :
    ∀ i, ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
      HasNaturalLocalRestrictionMass sets ν

/-- One scalar natural-mass condition passes to the weak limit law. -/
theorem NaturalRestrictionLawClosureInput.limit_mass_natural_ae
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    {sets : ℕ → κ → Set (MarkedSpectralSpace Unit)}
    (input : NaturalRestrictionLawClosureInput L μs μ sets)
    (n : ℕ) (k : κ) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      localRestrictionMass sets n k ν ∈
        Set.range ((↑) : ℕ → NNReal) := by
  let N : Set NNReal := Set.range ((↑) : ℕ → NNReal)
  have hmap_meas (ρ : ProbabilityMeasure VagueRationalWindowState) :
      Measurable (localRestrictionMass sets n k) :=
    measurable_localRestrictionMass sets input.sets_measurable n k
  have hsupported (i : α) :
      (localRestrictionMassLaw (μs i) sets n k : Measure NNReal) Nᶜ = 0 := by
    change Measure.map (localRestrictionMass sets n k)
      (μs i : Measure VagueRationalWindowState) Nᶜ = 0
    rw [Measure.map_apply (hmap_meas (μs i))
      isClosed_range_natCast_nnreal.measurableSet.compl]
    have hae :
        ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
          localRestrictionMass sets n k ν ∈ N :=
      (input.approximants_natural i).mono fun ν hν => hν n k
    have hpre :
        (localRestrictionMass sets n k) ⁻¹' Nᶜ =
          {ν | localRestrictionMass sets n k ν ∉ N} := by
      ext ν
      simp
    rw [hpre]
    exact ae_iff.mp hae
  have hlimit :
      (localRestrictionMassLaw μ sets n k : Measure NNReal) Nᶜ = 0 :=
    measure_compl_closed_eq_zero_of_tendsto
      (input.mass_laws_tendsto n k) N
      isClosed_range_natCast_nnreal hsupported
  change Measure.map (localRestrictionMass sets n k)
    (μ : Measure VagueRationalWindowState) Nᶜ = 0 at hlimit
  rw [Measure.map_apply (hmap_meas μ)
    isClosed_range_natCast_nnreal.measurableSet.compl] at hlimit
  rw [ae_iff]
  have hpre :
      (localRestrictionMass sets n k) ⁻¹' Nᶜ =
        {ν | localRestrictionMass sets n k ν ∉ N} := by
    ext ν
    simp
  rw [← hpre]
  exact hlimit

/-- Countably many scalar conclusions combine to almost-sure natural-valued
restriction masses for the whole determining family. -/
theorem NaturalRestrictionLawClosureInput.limit_natural_ae
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} [Countable κ]
    {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    {sets : ℕ → κ → Set (MarkedSpectralSpace Unit)}
    (input : NaturalRestrictionLawClosureInput L μs μ sets) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      HasNaturalLocalRestrictionMass sets ν := by
  change ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
    ∀ n k, localRestrictionMass sets n k ν ∈
      Set.range ((↑) : ℕ → NNReal)
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro k
  exact input.limit_mass_natural_ae n k

/-- Closed-carrier data which transfers projective consistency to a
boundary-regular limit law. -/
structure ConsistentLimitLawClosureInput
    [OpensMeasurableSpace VagueRationalWindowState]
    {α : Type v} (L : Filter α)
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  ambient_law_tendsto : Tendsto μs L (𝓝 μ)
  carrier : Set VagueRationalWindowState
  carrier_closed : IsClosed carrier
  approximants_supported :
    ∀ i, (μs i : Measure VagueRationalWindowState) carrierᶜ = 0
  consistent_of_mem_of_boundary_regular :
    ∀ ν, ν ∈ carrier → HasNullMarkedWindowBoundaries ν →
      IsConsistentLocalWindowEncoding ν

/-- The limit law is almost surely consistent once it is almost surely
boundary regular. -/
theorem ConsistentLimitLawClosureInput.limit_consistent_ae
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : ConsistentLimitLawClosureInput L μs μ)
    (hboundary :
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      IsConsistentLocalWindowEncoding ν := by
  have hcarrier :
      (μ : Measure VagueRationalWindowState) input.carrierᶜ = 0 :=
    measure_compl_closed_eq_zero_of_tendsto input.ambient_law_tendsto
      input.carrier input.carrier_closed input.approximants_supported
  have hmem :
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        ν ∈ input.carrier := by
    rw [ae_iff]
    convert hcarrier using 1
  filter_upwards [hmem, hboundary] with ν hν hνboundary
  exact input.consistent_of_mem_of_boundary_regular ν hν hνboundary

/-- Complete law-level closure input for all translated rational families. -/
structure BoundaryRegularLimitLawInput
    [OpensMeasurableSpace VagueRationalWindowState]
    {α : Type v} (L : Filter α)
    (μs : α → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  consistency : ConsistentLimitLawClosureInput L μs μ
  natural :
    ∀ s : ℝ, NaturalRestrictionLawClosureInput L μs μ
      (shiftedRationalDeterminingFamily s)

/-- The bundled point-state associated with one translated rational
determining family. -/
abbrev ShiftedRationalWindowPointState (s : ℝ) :=
  LocalPointMeasureStateSpace Unit (ℚ × ℚ)
    (shiftedRationalDeterminingFamily s)

/-- A boundary-avoiding translate makes the weak limit law almost surely
supported on projectively consistent encodings with natural-valued counts on
a countable dense interval family. -/
theorem BoundaryRegularLimitLawInput.exists_shift_ae_consistent_integer
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (endpointInput : BoundaryAvoidingEndpointInput μ)
    (input : BoundaryRegularLimitLawInput L μs μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        IsConsistentLocalWindowEncoding ν ∧
        HasNaturalLocalRestrictionMass
          (shiftedRationalDeterminingFamily s) ν) := by
  obtain ⟨s, hdense, hcount, hboundary⟩ :=
    endpointInput.exists_shift_ae_nullBoundaries
  have hconsistent :=
    input.consistency.limit_consistent_ae (hboundary.mono fun ν hν => hν.1)
  have hnatural := (input.natural s).limit_natural_ae
  refine ⟨s, hdense, hcount, ?_⟩
  filter_upwards [hboundary, hconsistent, hnatural] with ν hb hc hn
  exact ⟨hb.1, hb.2, hc, hn⟩

/-- Equivalently, almost every boundary-regular weak limit encoding lifts to
the bundled consistent integer local point-state space for the selected dense
endpoint family. -/
theorem BoundaryRegularLimitLawInput.exists_shift_ae_lifts_toPointState
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (endpointInput : BoundaryAvoidingEndpointInput μ)
    (input : BoundaryRegularLimitLawInput L μs μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        ∃ ξ : ShiftedRationalWindowPointState s, ξ.1 = ν) := by
  obtain ⟨s, hdense, hcount, hae⟩ :=
    input.exists_shift_ae_consistent_integer endpointInput
  refine ⟨s, hdense, hcount, ?_⟩
  filter_upwards [hae] with ν hν
  exact ⟨hν.1, hν.2.1, ⟨⟨ν, hν.2.2.1, hν.2.2.2⟩, rfl⟩⟩

end CoareaNative.BlockBand
