module

public import BlockBand.Coarea.Native.BlockBand.Counting.VagueLimitPointMeasureClosure
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Topology.Instances.Rat

/-!
# Boundary-avoiding endpoint families

A fixed countable family of sharp intervals need not be a continuity family
for an arbitrary random measure: the law may put an atom at one of its
endpoints.  The correct deterministic device is to translate the rationals.
If the exceptional endpoints are countable, then the exceptional translations
are countable as well, so one may choose `s` such that every `s + q`, `q ∈ ℚ`,
is a continuity point simultaneously for every local coordinate.

This module proves that selection argument and its law-level almost-sure
consequence.  The input structure deliberately records the exact remaining
probabilistic obligation: measurability of the singleton-mass events and a
countable exceptional set outside which those events are null.  In an
application this is supplied by the standard atom-countability/Fubini
argument.  It is not silently inferred from weak convergence.

The standard exhaustion endpoints `±m` are recorded separately.  This is
necessary: translating the rational family cannot alter the already fixed
windows `[-m,m]` used by `LocalWindowMeasureEncoding`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The countable dense family obtained by translating the rational numbers. -/
def shiftedRationalEndpoints (s : ℝ) : Set ℝ :=
  Set.range fun q : ℚ => s + (q : ℝ)

/-- A translated rational endpoint family is countable. -/
theorem countable_shiftedRationalEndpoints (s : ℝ) :
    (shiftedRationalEndpoints s).Countable :=
  Set.countable_range _

/-- A translated rational endpoint family is dense. -/
theorem dense_shiftedRationalEndpoints (s : ℝ) :
    Dense (shiftedRationalEndpoints s) := by
  rw [dense_iff_closure_eq]
  change closure (Set.range fun q : ℚ => s + (q : ℝ)) = Set.univ
  rw [show Set.range (fun q : ℚ => s + (q : ℝ)) =
      (Homeomorph.addLeft s) '' Set.range ((↑) : ℚ → ℝ) by
        ext x
        simp only [Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨q, rfl⟩
          exact ⟨(q : ℝ), ⟨q, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
          exact ⟨q, rfl⟩]
  rw [← (Homeomorph.addLeft s).image_closure,
    Rat.denseRange_cast.closure_range]
  simpa only [Set.image_univ] using
    (Homeomorph.addLeft s).surjective.range_eq

/-- Shifts which make some translated rational hit one of the exceptional
endpoints in one of the countably many local coordinates. -/
def endpointBadShifts (exceptional : ℕ → Set ℝ) : Set ℝ :=
  ⋃ n, ⋃ q : ℚ, (fun x : ℝ => x - (q : ℝ)) '' exceptional n

/-- Countably many countable exceptional endpoint sets give only countably
many bad rational translations. -/
theorem countable_endpointBadShifts
    {exceptional : ℕ → Set ℝ}
    (hcount : ∀ n, (exceptional n).Countable) :
    (endpointBadShifts exceptional).Countable := by
  apply Set.countable_iUnion
  intro n
  apply Set.countable_iUnion
  intro q
  exact (hcount n).image _

/-- There is a rational translate avoiding every exceptional endpoint in
every coordinate. -/
theorem exists_shiftedRationalEndpoints_avoids
    {exceptional : ℕ → Set ℝ}
    (hcount : ∀ n, (exceptional n).Countable) :
    ∃ s : ℝ, ∀ n (q : ℚ), s + (q : ℝ) ∉ exceptional n := by
  have hbad := countable_endpointBadShifts hcount
  have hne : endpointBadShifts exceptional ≠ Set.univ := by
    intro h
    apply Cardinal.not_countable_real
    rw [← h]
    exact hbad
  have hex : ∃ s : ℝ, s ∉ endpointBadShifts exceptional := by
    by_contra h
    push Not at h
    exact hne (Set.eq_univ_of_forall h)
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, fun n q hmem => hs ?_⟩
  simp only [endpointBadShifts, Set.mem_iUnion]
  exact ⟨n, q, s + (q : ℝ), hmem, by ring⟩

/-- The vertical endpoint fiber in the marked spectral space. -/
def spectralEndpointFiber (x : ℝ) : Set (MarkedSpectralSpace Unit) :=
  ({x} : Set ℝ) ×ˢ Set.univ

/-- The event that coordinate `n` charges the spectral endpoint `x`. -/
def coordinateChargesEndpoint (n : ℕ) (x : ℝ) :
    Set VagueRationalWindowState :=
  {ν | (ν n : Measure (MarkedSpectralSpace Unit))
    (spectralEndpointFiber x) ≠ 0}

/-- Singleton endpoint-mass events are Borel in the ambient weak-product
state.  This uses the Giry measurable structure on finite measures together
with the measurable coordinate projection. -/
theorem measurableSet_coordinateChargesEndpoint (n : ℕ) (x : ℝ) :
    MeasurableSet (coordinateChargesEndpoint n x) := by
  have hset : MeasurableSet (spectralEndpointFiber x) :=
    (measurableSet_singleton x).prod MeasurableSet.univ
  have hmeasure :
      Measurable (fun ν : VagueRationalWindowState =>
        (ν n : Measure (MarkedSpectralSpace Unit))) :=
    measurable_subtype_coe.comp (measurable_pi_apply n)
  have hmass :
      Measurable (fun ν : VagueRationalWindowState =>
        (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber x)) :=
    (Measure.measurable_coe hset).comp hmeasure
  have hzero : MeasurableSet
      {ν : VagueRationalWindowState |
        (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber x) = 0} :=
    (measurableSet_singleton (0 : ENNReal)).preimage hmass
  convert hzero.compl using 1
  ext ν
  simp [coordinateChargesEndpoint]

/-- Closed intervals whose endpoints run through one translated rational
family.  The coordinate argument is retained so this has exactly the shape
required by `HasNullLocalRestrictionBoundaries`. -/
def shiftedRationalDeterminingFamily (s : ℝ)
    (_n : ℕ) (q : ℚ × ℚ) : Set (MarkedSpectralSpace Unit) :=
  Set.Icc (s + (q.1 : ℝ)) (s + (q.2 : ℝ)) ×ˢ Set.univ

/-- Every shifted rational determining interval is Borel. -/
theorem measurableSet_shiftedRationalDeterminingFamily
    (s : ℝ) (n : ℕ) (q : ℚ × ℚ) :
    MeasurableSet (shiftedRationalDeterminingFamily s n q) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- The measurable event on which all translated rational endpoints and all
fixed exhaustion endpoints carry zero coordinate mass. -/
def boundaryAvoidingEndpointEvent (s : ℝ) :
    Set VagueRationalWindowState :=
  {ν |
    (∀ n (q : ℚ),
      (ν n : Measure (MarkedSpectralSpace Unit))
        (spectralEndpointFiber (s + (q : ℝ))) = 0) ∧
    (∀ n (m : ℕ),
      (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber (m : ℝ)) = 0 ∧
      (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber (-(m : ℝ))) = 0)}

/-- The simultaneous endpoint-regularity event is Borel. -/
theorem measurableSet_boundaryAvoidingEndpointEvent (s : ℝ) :
    MeasurableSet (boundaryAvoidingEndpointEvent s) := by
  let shiftedGood : Set VagueRationalWindowState :=
    ⋂ n, ⋂ q : ℚ, (coordinateChargesEndpoint n (s + (q : ℝ)))ᶜ
  let standardGood : Set VagueRationalWindowState :=
    ⋂ n, ⋂ m : ℕ,
      (coordinateChargesEndpoint n (m : ℝ))ᶜ ∩
      (coordinateChargesEndpoint n (-(m : ℝ)))ᶜ
  have hshifted : MeasurableSet shiftedGood := by
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro q
    exact (measurableSet_coordinateChargesEndpoint n
      (s + (q : ℝ))).compl
  have hstandard : MeasurableSet standardGood := by
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro m
    exact (measurableSet_coordinateChargesEndpoint n (m : ℝ)).compl.inter
      (measurableSet_coordinateChargesEndpoint n (-(m : ℝ))).compl
  convert hshifted.inter hstandard using 1
  ext ν
  simp [shiftedGood, standardGood, boundaryAvoidingEndpointEvent,
    coordinateChargesEndpoint]

/-- Exact law-level hypotheses needed by the boundary-avoidance selection.

`standard_endpoints_regular` is separate from rational translation because
the ambient encoding has already fixed the exhaustion windows `[-m,m]`.
Measurability of all endpoint events was proved above.  The construction of
`exceptional` by atom countability/Fubini is the downstream model-specific
obligation. -/
structure BoundaryAvoidingEndpointInput
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  exceptional : ℕ → Set ℝ
  exceptional_countable : ∀ n, (exceptional n).Countable
  endpoint_event_null_of_not_mem :
    ∀ n x, x ∉ exceptional n →
      (μ : Measure VagueRationalWindowState)
        (coordinateChargesEndpoint n x) = 0
  standard_endpoints_regular :
    ∀ n m, (m : ℝ) ∉ exceptional n ∧ -(m : ℝ) ∉ exceptional n

/-- A measure which gives zero mass to both endpoint fibers gives zero mass
to the frontier of the corresponding marked closed interval.  The empty
interval case is included. -/
theorem measure_frontier_Icc_prod_univ_eq_zero_of_endpoints
    (ν : Measure (MarkedSpectralSpace Unit)) (a b : ℝ)
    (ha : ν (spectralEndpointFiber a) = 0)
    (hb : ν (spectralEndpointFiber b) = 0) :
    ν (frontier (Set.Icc a b ×ˢ (Set.univ : Set Unit))) = 0 := by
  by_cases hab : a ≤ b
  · rw [frontier_prod_univ_eq, frontier_Icc hab]
    apply measure_mono_null _ (measure_union_null ha hb)
    rintro ⟨x, u⟩ ⟨hx, -⟩
    rcases hx with rfl | rfl
    · exact Set.mem_union_left _ ⟨Set.mem_singleton _, Set.mem_univ _⟩
    · exact Set.mem_union_right _ ⟨Set.mem_singleton _, Set.mem_univ _⟩
  · have hempty : Set.Icc a b = (∅ : Set ℝ) := Set.Icc_eq_empty hab
    simp [hempty]

/-- A single null endpoint event gives almost-sure zero endpoint mass. -/
theorem BoundaryAvoidingEndpointInput.ae_endpointMass_eq_zero
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ)
    {n : ℕ} {x : ℝ} (hx : x ∉ input.exceptional n) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      (ν n : Measure (MarkedSpectralSpace Unit))
        (spectralEndpointFiber x) = 0 := by
  rw [ae_iff]
  simpa [coordinateChargesEndpoint] using
    input.endpoint_event_null_of_not_mem n x hx

/-- The selected shifted rational family is simultaneously atom-free in every
coordinate, almost surely under the supplied law. -/
theorem BoundaryAvoidingEndpointInput.exists_shift_ae_endpointMass_eq_zero
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        ∀ n (q : ℚ),
          (ν n : Measure (MarkedSpectralSpace Unit))
            (spectralEndpointFiber (s + (q : ℝ))) = 0) := by
  obtain ⟨s, hs⟩ :=
    exists_shiftedRationalEndpoints_avoids input.exceptional_countable
  refine ⟨s, dense_shiftedRationalEndpoints s,
    countable_shiftedRationalEndpoints s, ?_⟩
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro q
  exact input.ae_endpointMass_eq_zero (hs n q)

/-- The already fixed integer exhaustion endpoints are simultaneously
atom-free almost surely. -/
theorem BoundaryAvoidingEndpointInput.ae_standardEndpointMass_eq_zero
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      ∀ n (m : ℕ),
        (ν n : Measure (MarkedSpectralSpace Unit))
            (spectralEndpointFiber (m : ℝ)) = 0 ∧
        (ν n : Measure (MarkedSpectralSpace Unit))
            (spectralEndpointFiber (-(m : ℝ))) = 0 := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro m
  exact (input.ae_endpointMass_eq_zero
    (input.standard_endpoints_regular n m).1).and
    (input.ae_endpointMass_eq_zero
      (input.standard_endpoints_regular n m).2)

/-- Consequently the fixed sharp exhaustion windows have null frontier
simultaneously almost surely. -/
theorem BoundaryAvoidingEndpointInput.ae_hasNullMarkedWindowBoundaries
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ) :
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      HasNullMarkedWindowBoundaries ν := by
  filter_upwards [input.ae_standardEndpointMass_eq_zero] with ν hν
  intro n m
  unfold markedSpectralWindow
  exact measure_frontier_Icc_prod_univ_eq_zero_of_endpoints
    (ν n : Measure (MarkedSpectralSpace Unit)) (-(m : ℝ)) (m : ℝ)
    (hν n m).2 (hν n m).1

/-- One may choose a countable dense interval family whose every frontier is
null simultaneously almost surely under the law. -/
theorem BoundaryAvoidingEndpointInput.exists_shift_ae_nullBoundaries
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν) := by
  obtain ⟨s, hdense, hcount, hshift⟩ :=
    input.exists_shift_ae_endpointMass_eq_zero
  refine ⟨s, hdense, hcount, ?_⟩
  filter_upwards [input.ae_hasNullMarkedWindowBoundaries, hshift] with ν hwindow hendpoints
  refine ⟨hwindow, ?_⟩
  intro n q
  unfold shiftedRationalDeterminingFamily
  exact measure_frontier_Icc_prod_univ_eq_zero_of_endpoints
    (ν n : Measure (MarkedSpectralSpace Unit))
    (s + (q.1 : ℝ)) (s + (q.2 : ℝ))
    (hendpoints n q.1) (hendpoints n q.2)

/-- Law-level form of the selection: there is a translated rational family
whose simultaneous endpoint-regularity event is measurable and has null
complement. -/
theorem BoundaryAvoidingEndpointInput.exists_shift_boundaryEvent_compl_null
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : BoundaryAvoidingEndpointInput μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      MeasurableSet (boundaryAvoidingEndpointEvent s) ∧
      (μ : Measure VagueRationalWindowState)
        (boundaryAvoidingEndpointEvent s)ᶜ = 0 := by
  obtain ⟨s, hdense, hcount, hshift⟩ :=
    input.exists_shift_ae_endpointMass_eq_zero
  have hstandard := input.ae_standardEndpointMass_eq_zero
  refine ⟨s, hdense, hcount,
    measurableSet_boundaryAvoidingEndpointEvent s, ?_⟩
  have hae :
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        ν ∈ boundaryAvoidingEndpointEvent s := by
    filter_upwards [hshift, hstandard] with ν hνshift hνstandard
    exact ⟨hνshift, hνstandard⟩
  convert ae_iff.mp hae using 1

end CoareaNative.BlockBand
