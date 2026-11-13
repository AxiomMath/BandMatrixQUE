module

public import BlockBand.Coarea.Native.BlockBand.Counting.VagueRationalWindowTopology
public import BlockBand.Coarea.Native.BlockBand.Counting.IntegerPointMeasureClosure

/-!
# Boundary-regular closure of vague rational-window limits

This module carries the ambient weak-product construction one step further.
For a *particular* coordinatewise weak limit, null boundaries of the chosen
countable rational windows imply convergence of all corresponding counts by
the finite-measure Portmanteau theorem.  Hence integer-valuedness passes to the
limit without assuming continuity of sharp restriction.

Projective consistency is separated from integer closure.  It follows once the
sharp restrictions along the particular convergent net converge; this is a
local boundary-regular assertion, not continuity of restriction on the whole
finite-measure space.  The resulting limit is bundled as
`RationalWindowPointState`.

For probability laws, PSSS alone already gives the ambient weak subsequence and
all finite-matrix counting estimates.  Proving that the limiting *law* is
concentrated on boundary-regular encodings needs a measurable
boundary-avoidance/disintegration argument.  Here boundary regularity is an
explicit hypothesis (the law-level form is `BoundaryRegularLimitLawInput`),
rather than treating closed-window counts as continuous.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u v w

/-- Null boundaries plus ambient coordinatewise weak convergence automatically
supply convergence of every chosen local restriction mass. -/
theorem localRestrictionMassesConverge_of_tendsto_of_nullBoundaries
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [Nonempty (MarkedSpectralSpace Mark)]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {l : Filter α}
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hν : Tendsto νs l (𝓝 ν))
    (hboundary : HasNullLocalRestrictionBoundaries sets ν) :
    LocalRestrictionMassesConverge sets l νs ν := by
  intro n k
  have hcoord : Tendsto (fun q => νs q n) l (𝓝 (ν n)) :=
    ((continuous_apply n).tendsto ν).comp hν
  have happly := FiniteMeasure.tendsto_apply_of_null_frontier
    hcoord (by
      apply ENNReal.coe_eq_zero.mp
      simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        hboundary n k)
  simpa [FiniteMeasure.restrict_mass,
    measurableSet_rationalWindowDeterminingFamily] using happly

/-- Integer local counts pass automatically to a boundary-regular ambient
weak limit.  Unlike the older abstract interface, no separate mass-convergence
hypothesis is required. -/
theorem hasNaturalLocalRestrictionMass_of_vague_tendsto
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [Nonempty (MarkedSpectralSpace Mark)]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {l : Filter α} [NeBot l]
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hnat : ∀ q, HasNaturalLocalRestrictionMass sets (νs q))
    (hν : Tendsto νs l (𝓝 ν))
    (hboundary : HasNullLocalRestrictionBoundaries sets ν) :
    HasNaturalLocalRestrictionMass sets ν := by
  exact hasNaturalLocalRestrictionMass_of_tendsto
    (L := l) sets hnat
    (localRestrictionMassesConverge_of_tendsto_of_nullBoundaries
      sets hν hboundary)

/-- Boundary-regular closure data for one convergent net.  The sharp
restriction field is local to this net and limit; it does not assert the false
global continuity of closed-window restriction. -/
structure VagueLimitPointMeasureClosureInput
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [Nonempty (MarkedSpectralSpace Mark)]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} (l : Filter α)
    (νs : α → LocalWindowMeasureEncoding Mark)
    (ν : LocalWindowMeasureEncoding Mark) : Prop where
  approximants_consistent : ∀ q, IsConsistentLocalWindowEncoding (νs q)
  approximants_integer : ∀ q, HasNaturalLocalRestrictionMass sets (νs q)
  encoding_tendsto : Tendsto νs l (𝓝 ν)
  marked_window_boundaries_null : HasNullMarkedWindowBoundaries ν
  sharp_restrictions_converge : SharpWindowRestrictionsConverge l νs ν
  determining_boundaries_null : HasNullLocalRestrictionBoundaries sets ν

/-- The boundary-regular input supplies the older closure interface, with
restriction-mass convergence now proved rather than assumed. -/
theorem VagueLimitPointMeasureClosureInput.toIntegerPointMeasureClosureInput
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [Nonempty (MarkedSpectralSpace Mark)]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {l : Filter α}
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (input : VagueLimitPointMeasureClosureInput sets l νs ν) :
    IntegerPointMeasureClosureInput sets l νs ν where
  approximants_consistent := input.approximants_consistent
  approximants_integer := input.approximants_integer
  encoding_tendsto := input.encoding_tendsto
  limit_boundary_null := input.marked_window_boundaries_null
  sharp_restrictions_converge := input.sharp_restrictions_converge
  determining_boundaries_null := input.determining_boundaries_null
  restriction_masses_converge :=
    localRestrictionMassesConverge_of_tendsto_of_nullBoundaries
      sets input.encoding_tendsto input.determining_boundaries_null

/-- Boundary-regular vague closure reconstructs a bundled local point state.
All integer-valued restriction masses are obtained from Portmanteau rather
than postulated. -/
def VagueLimitPointMeasureClosureInput.toLocalPointMeasureStateSpace
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [Nonempty (MarkedSpectralSpace Mark)]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {l : Filter α} [NeBot l]
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (input : VagueLimitPointMeasureClosureInput sets l νs ν) :
    LocalPointMeasureStateSpace Mark κ sets :=
  ⟨ν,
    isConsistent_of_nullBoundaries_of_sharpRestrictionsConverge
      input.approximants_consistent input.encoding_tendsto
      input.marked_window_boundaries_null
      input.sharp_restrictions_converge,
    hasNaturalLocalRestrictionMass_of_vague_tendsto sets
      input.approximants_integer input.encoding_tendsto
      input.determining_boundaries_null⟩

/-- Specialization of boundary-regular closure to the rational-window state
used by the BlockGUE counting argument. -/
def VagueLimitPointMeasureClosureInput.toRationalWindowPointState
    {α : Type*} {l : Filter α} [NeBot l]
    {νs : α → VagueRationalWindowState}
    {ν : VagueRationalWindowState}
    (input : VagueLimitPointMeasureClosureInput
      rationalWindowDeterminingFamily l νs ν) :
    RationalWindowPointState :=
  input.toLocalPointMeasureStateSpace rationalWindowDeterminingFamily

/-- For a boundary-regular rational-window limit, every rational count is the
limit of the corresponding integer counts and is itself a natural number. -/
theorem VagueLimitPointMeasureClosureInput.rational_count_tendsto_and_natural
    {α : Type*} {l : Filter α} [NeBot l]
    {νs : α → VagueRationalWindowState}
    {ν : VagueRationalWindowState}
    (input : VagueLimitPointMeasureClosureInput
      rationalWindowDeterminingFamily l νs ν)
    (n : ℕ) (q : ℚ × ℚ) :
    Tendsto (fun j => ((νs j n).restrict
        (rationalWindowDeterminingFamily n q)).mass) l
      (𝓝 (((ν n).restrict
        (rationalWindowDeterminingFamily n q)).mass)) ∧
    ((ν n).restrict (rationalWindowDeterminingFamily n q)).mass ∈
      Set.range ((↑) : ℕ → NNReal) := by
  have hmass := localRestrictionMassesConverge_of_tendsto_of_nullBoundaries
    rationalWindowDeterminingFamily input.encoding_tendsto
      input.determining_boundaries_null
  exact ⟨hmass n q,
    (input.toRationalWindowPointState.2.2 n q)⟩

/-- Paper-facing PSSS conclusion in the ambient vague-product topology.
It contains a weak subsequence and all finite-matrix factorial,
exponential, and close-pair bounds, and assumes no sharp-window continuity. -/
def PSSSVagueCountingConclusion
    [TopologicalSpace (ProbabilityMeasure VagueRationalWindowState)]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input) : Prop :=
  (∃ μ : ProbabilityMeasure VagueRationalWindowState,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ)) ∧
  (∀ i (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
    ∫ ω, ((BlockGUE.intervalCount (seq.model i) (seq.deformation i)
      (Set.Icc a b) ω).descFactorial r : ℝ) ∂(seq.model i).P ≤
      (input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) * (b - a)) ^ r) ∧
  (∀ i (R t : ℝ), 0 ≤ R → 0 ≤ t →
    ∫ ω, Real.exp (t *
      (BlockGUE.unfoldedIntervalCount (seq.model i) (seq.deformation i)
        (seq.energy i) (seq.scale i) (seq.density i) R ω : ℝ))
        ∂(seq.model i).P ≤
      Real.exp (2 * R * (input.C / seq.density i) * (Real.exp t - 1))) ∧
  (∀ i (a b : ℝ), a ≤ b →
    ∫ ω, ((BlockGUE.intervalCount (seq.model i) (seq.deformation i)
      (Set.Icc a b) ω).descFactorial 2 : ℝ) ∂(seq.model i).P ≤
      (input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) * (b - a)) ^ 2)

/-- PSSS alone supplies the full ambient counting conclusion, with no globally
false continuity assumptions. -/
theorem psssVagueCounting
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    (input : PSSSInput.{u}) (seq : PSSSRationalWindowSequence input) :
    PSSSVagueCountingConclusion seq := by
  refine ⟨seq.exists_vague_weak_subsequence, ?_, ?_, ?_⟩
  · intro i a b hab r hr
    exact psss_factorialCount input (seq.hd i) (seq.model i)
      (seq.deformation i) a b hab r hr
  · intro i R t hR ht
    exact psss_unfoldedCountExponential input (seq.hd i) (seq.model i)
      (seq.deformation i) (seq.energy i) (seq.scale i) (seq.density i)
      R t (seq.scale_pos i) (seq.density_pos i) hR
      (seq.dimension_le_scale i) ht
  · intro i a b hab
    exact psss_closePairCount input (seq.hd i) (seq.model i)
      (seq.deformation i) a b hab

end CoareaNative.BlockBand
