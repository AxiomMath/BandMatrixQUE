module

public import BlockBand.Coarea.Native.BlockBand.Counting.BoundaryRegularLimitLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Boundary avoidance from finite endpoint intensities

This module discharges the countability part of
`BoundaryAvoidingEndpointInput` from a first-intensity measure.  For
one local coordinate, the exceptional endpoints are the atoms of a finite
measure on the spectral line.  Atom countability makes this exceptional set
countable.  If the expected random mass of every vertical singleton agrees
with that intensity, a non-atom endpoint is charged with probability zero.

The already fixed exhaustion endpoints `±m` cannot be repaired by translating
the rational determining family.  Their nullity is therefore retained as an
explicit hypothesis.  In the important diffuse-intensity specialization this
hypothesis is automatic and the exceptional sets are empty.

This is a law-level construction only.  A model application must still build
the finite intensity and prove the displayed singleton expectation identity,
for example from the paper's uniform first-moment/Wegner estimate.  No
arbitrary-law diffuseness is asserted.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- The atoms of a finite measure, expressed through singleton masses. -/
def finiteMeasureAtomSet (ν : FiniteMeasure ℝ) : Set ℝ :=
  {x | (ν : Measure ℝ) {x} ≠ 0}

/-- A finite measure has only countably many singleton atoms.

The proof decomposes the atoms into the finite sets whose masses are bounded
below by a fixed positive dyadic threshold. -/
theorem countable_finiteMeasureAtomSet (ν : FiniteMeasure ℝ) :
    (finiteMeasureAtomSet ν).Countable := by
  have hthreshold (k : ℕ) :
      Set.Finite {x : ℝ | (2 : ENNReal)⁻¹ ^ k ≤ (ν : Measure ℝ) {x}} := by
    have hinv : 0 < (2 : ENNReal)⁻¹ :=
      ENNReal.inv_pos.2 (by norm_num)
    have hpow : 0 < (2 : ENNReal)⁻¹ ^ k := ENNReal.pow_pos hinv k
    apply Measure.finite_const_le_meas_of_disjoint_iUnion
      (ν : Measure ℝ) hpow
    · intro x
      exact measurableSet_singleton x
    · intro x y hxy
      exact Set.disjoint_singleton.2 hxy
    · have hfinite : (ν : Measure ℝ) Set.univ ≠ ∞ :=
        (measure_lt_top (ν : Measure ℝ) Set.univ).ne
      simp
  rw [show finiteMeasureAtomSet ν =
      ⋃ k : ℕ, {x : ℝ | (2 : ENNReal)⁻¹ ^ k ≤
        (ν : Measure ℝ) {x}} by
    ext x
    simp only [finiteMeasureAtomSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hx
      exact ⟨k, hk.le⟩
    · rintro ⟨k, hk⟩ hzero
      rw [hzero] at hk
      have hinv : 0 < (2 : ENNReal)⁻¹ :=
        ENNReal.inv_pos.2 (by norm_num)
      exact (not_le_of_gt (ENNReal.pow_pos hinv k)) hk]
  exact Set.countable_iUnion fun k => (hthreshold k).countable

/-- The endpoint mass in one local coordinate is a measurable
`ENNReal`-valued random variable. -/
theorem measurable_coordinateEndpointMass (n : ℕ) (x : ℝ) :
    Measurable (fun ν : VagueRationalWindowState =>
      (ν n : Measure (MarkedSpectralSpace Unit))
        (spectralEndpointFiber x)) := by
  have hset : MeasurableSet (spectralEndpointFiber x) :=
    (measurableSet_singleton x).prod MeasurableSet.univ
  exact (Measure.measurable_coe hset).comp
    (measurable_subtype_coe.comp (measurable_pi_apply n))

/-- Finite first-intensity data sufficient to construct the exceptional
endpoint sets for a weak limit law.

`singleton_expectation` fixes the normalization: the intensity singleton mass
is the expectation of the full vertical endpoint fiber in coordinate `n`.
The separate standard-endpoint field is unavoidable for the preselected
windows `[-m,m]`. -/
structure EndpointIntensityBoundaryInput
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  intensity : ℕ → FiniteMeasure ℝ
  singleton_expectation :
    ∀ n x,
      ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber x)
        ∂(μ : Measure VagueRationalWindowState) =
      (intensity n : Measure ℝ) {x}
  standard_endpoint_null :
    ∀ n m,
      (intensity n : Measure ℝ) {(m : ℝ)} = 0 ∧
      (intensity n : Measure ℝ) {-(m : ℝ)} = 0

/-- Outside the atom set of the finite intensity, the random coordinate gives
zero mass to the endpoint almost surely. -/
theorem EndpointIntensityBoundaryInput.endpoint_event_null_of_not_atom
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : EndpointIntensityBoundaryInput μ)
    {n : ℕ} {x : ℝ} (hx : x ∉ finiteMeasureAtomSet (input.intensity n)) :
    (μ : Measure VagueRationalWindowState)
      (coordinateChargesEndpoint n x) = 0 := by
  let f : VagueRationalWindowState → ENNReal := fun ν =>
    (ν n : Measure (MarkedSpectralSpace Unit)) (spectralEndpointFiber x)
  have hf : Measurable f := measurable_coordinateEndpointMass n x
  have hlintegral : ∫⁻ ν, f ν ∂(μ : Measure VagueRationalWindowState) = 0 := by
    rw [input.singleton_expectation n x]
    simpa [finiteMeasureAtomSet] using hx
  have hae : f =ᵐ[(μ : Measure VagueRationalWindowState)] 0 :=
    (lintegral_eq_zero_iff hf).mp hlintegral
  rw [coordinateChargesEndpoint, ← ae_iff]
  filter_upwards [hae] with ν hν
  exact hν

/-- Finite endpoint intensities with null standard endpoints construct the
complete boundary-avoidance input used by `BoundaryRegularLimitLawInput`. -/
def EndpointIntensityBoundaryInput.toBoundaryAvoidingEndpointInput
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : EndpointIntensityBoundaryInput μ) :
    BoundaryAvoidingEndpointInput μ where
  exceptional n := finiteMeasureAtomSet (input.intensity n)
  exceptional_countable n := countable_finiteMeasureAtomSet (input.intensity n)
  endpoint_event_null_of_not_mem n x hx :=
    input.endpoint_event_null_of_not_atom hx
  standard_endpoints_regular n m := by
    constructor
    · simpa [finiteMeasureAtomSet] using
        (input.standard_endpoint_null n m).1
    · simpa [finiteMeasureAtomSet] using
        (input.standard_endpoint_null n m).2

/-- In particular, a diffuse finite intensity needs no exceptional endpoints:
every singleton endpoint is almost surely uncharged. -/
theorem EndpointIntensityBoundaryInput.ae_endpointMass_eq_zero_of_diffuse
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : EndpointIntensityBoundaryInput μ)
    (hdiffuse : ∀ n x, (input.intensity n : Measure ℝ) {x} = 0) :
    ∀ n x, ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      (ν n : Measure (MarkedSpectralSpace Unit))
        (spectralEndpointFiber x) = 0 := by
  intro n x
  have hx : x ∉ finiteMeasureAtomSet (input.intensity n) := by
    simpa [finiteMeasureAtomSet] using hdiffuse n x
  rw [ae_iff]
  simpa [coordinateChargesEndpoint] using
    input.endpoint_event_null_of_not_atom hx

/-- Diffuse endpoint intensity gives the exact input needed by the shifted
boundary-regular limit-law theorem, with empty exceptional sets. -/
def boundaryAvoidingEndpointInputOfDiffuseIntensity
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (intensity : ℕ → FiniteMeasure ℝ)
    (singleton_expectation :
      ∀ n x,
        ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
            (spectralEndpointFiber x)
          ∂(μ : Measure VagueRationalWindowState) =
        (intensity n : Measure ℝ) {x})
    (hdiffuse : ∀ n x, (intensity n : Measure ℝ) {x} = 0) :
    BoundaryAvoidingEndpointInput μ := by
  let input : EndpointIntensityBoundaryInput μ :=
    EndpointIntensityBoundaryInput.mk intensity singleton_expectation
      (fun n m => ⟨hdiffuse n (m : ℝ), hdiffuse n (-(m : ℝ))⟩)
  exact input.toBoundaryAvoidingEndpointInput

/-- Combining finite endpoint intensity with the law-level closure package
selects a dense continuity family on which the limit encoding is almost surely
consistent and integer-valued.  This is the direct bridge toward the counting
theorem; the intensity hypotheses are the remaining model-facing
first-moment obligations. -/
theorem BoundaryRegularLimitLawInput.exists_shift_ae_consistent_integer_of_intensity
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type*} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (intensityInput : EndpointIntensityBoundaryInput μ)
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
          (shiftedRationalDeterminingFamily s) ν) :=
  input.exists_shift_ae_consistent_integer
    intensityInput.toBoundaryAvoidingEndpointInput

/-- The same intensity construction yields almost-sure lifting to the bundled
local point-state space selected by the shifted dense endpoint family. -/
theorem BoundaryRegularLimitLawInput.exists_shift_ae_lifts_toPointState_of_intensity
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type*} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (intensityInput : EndpointIntensityBoundaryInput μ)
    (input : BoundaryRegularLimitLawInput L μs μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        ∃ ξ : ShiftedRationalWindowPointState s, ξ.1 = ν) :=
  input.exists_shift_ae_lifts_toPointState
    intensityInput.toBoundaryAvoidingEndpointInput

end CoareaNative.BlockBand
