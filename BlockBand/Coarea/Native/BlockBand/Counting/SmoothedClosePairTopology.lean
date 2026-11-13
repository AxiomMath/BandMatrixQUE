module

public import BlockBand.Coarea.Native.BlockBand.Counting.VagueRationalWindowTopology
public import BlockBand.Coarea.Native.BlockBand.Counting.MarkedProcessTightness
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Open smoothed multiplicity events for vague local configurations

The collision-exclusion step in the block-band paper passes a close-pair
estimate through weak convergence.  Sharp pair indicators are not continuous
on the ambient weak product.  This module supplies the standard replacement:
test local coordinates against bounded continuous nonnegative bump functions.
The resulting superlevel events are open, while an atom of mass at
least two is detected by any bump which equals one at that atom.

No existence of a particular bump family is hidden here.  The final coverage
theorem records exactly the point-separating property required of such a
family; constructing the paper's rational tent functions is a separate
one-dimensional task.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u

/-- Pairing of one local finite-measure coordinate with a bounded continuous
nonnegative test function. -/
def vagueLocalTestMass (n : ℕ)
    (f : BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal)
    (ν : VagueRationalWindowState) : NNReal :=
  (ν n).testAgainstNN f

/-- Smoothed local masses are continuous in the weak product topology. -/
theorem continuous_vagueLocalTestMass (n : ℕ)
    (f : BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    Continuous (vagueLocalTestMass n f) := by
  exact (FiniteMeasure.continuous_testAgainstNN_eval f).comp
    (continuous_localWindowMeasureEvaluation n)

/-- The event on which one local bump sees mass strictly greater than one. -/
def smoothedDoubleMassEvent (n : ℕ)
    (f : BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    Set VagueRationalWindowState :=
  {ν | 1 < vagueLocalTestMass n f ν}

/-- A smoothed double-mass event is open, exactly as required by the
Portmanteau lower bound. -/
theorem isOpen_smoothedDoubleMassEvent (n : ℕ)
    (f : BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    IsOpen (smoothedDoubleMassEvent n f) := by
  exact isOpen_lt continuous_const (continuous_vagueLocalTestMass n f)

/-- A countable (or arbitrary) family of bump tests gives the open close-pair
surrogate used in the weak-limit argument. -/
def smoothedClosePairEvent {κ : Type u} (n : ℕ)
    (f : κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    Set VagueRationalWindowState :=
  ⋃ k, smoothedDoubleMassEvent n (f k)

/-- The union of all smoothed witnesses is open. -/
theorem isOpen_smoothedClosePairEvent {κ : Type u} (n : ℕ)
    (f : κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    IsOpen (smoothedClosePairEvent n f) := by
  exact isOpen_iUnion fun k => isOpen_smoothedDoubleMassEvent n (f k)

/-- The corresponding event is Borel measurable. -/
theorem measurableSet_smoothedClosePairEvent
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} (n : ℕ)
    (f : κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal) :
    MeasurableSet (smoothedClosePairEvent n f) :=
  (isOpen_smoothedClosePairEvent n f).measurableSet

/-- A local multiplicity collision: one point carries mass at least
`2` in the `n`th finite-measure coordinate. -/
def localMultiplicityCollisionEvent (n : ℕ) :
    Set VagueRationalWindowState :=
  {ν | ∃ x : MarkedSpectralSpace Unit,
    (2 : ENNReal) ≤ (ν n : Measure (MarkedSpectralSpace Unit)) {x}}

/-- If a bump is one at an atom of multiplicity at least two, its integral is
strictly greater than one. -/
theorem one_lt_testAgainstNN_of_two_le_singleton
    (μ : FiniteMeasure (MarkedSpectralSpace Unit))
    (f : BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal)
    (x : MarkedSpectralSpace Unit) (hfx : f x = 1)
    (hx : (2 : ENNReal) ≤ (μ : Measure (MarkedSpectralSpace Unit)) {x}) :
    (1 : NNReal) < μ.testAgainstNN f := by
  apply ENNReal.coe_lt_coe.mp
  rw [FiniteMeasure.testAgainstNN_coe_eq]
  have hsingle : (2 : ENNReal) ≤
      ∫⁻ y in ({x} : Set (MarkedSpectralSpace Unit)), (f y : ENNReal) ∂(μ : Measure _) := by
    rw [lintegral_singleton]
    simpa [hfx] using hx
  have hmono :
      (∫⁻ y in ({x} : Set (MarkedSpectralSpace Unit)), (f y : ENNReal) ∂(μ : Measure _)) ≤
        ∫⁻ y, (f y : ENNReal) ∂(μ : Measure _) :=
    setLIntegral_le_lintegral _ _
  exact lt_of_lt_of_le (by norm_num : (1 : ENNReal) < 2)
    (hsingle.trans hmono)

/-- Any family which contains a unit bump at every point detects every local
multiplicity collision by an open smoothed event. -/
theorem localMultiplicityCollisionEvent_subset_smoothedClosePairEvent
    {κ : Type u} (n : ℕ)
    (f : κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal)
    (hcover : ∀ x : MarkedSpectralSpace Unit, ∃ k, f k x = 1) :
    localMultiplicityCollisionEvent n ⊆ smoothedClosePairEvent n f := by
  rintro ν ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hcover x
  rw [smoothedClosePairEvent, Set.mem_iUnion]
  refine ⟨k, ?_⟩
  exact one_lt_testAgainstNN_of_two_le_singleton (ν n) (f k) x hk hx

/-- Weak convergence transfers any uniform finite-volume bound for the
smoothed close-pair event to the limiting law. -/
theorem limit_smoothedClosePairEvent_le
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type*} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (hlim : Tendsto μs L (𝓝 μ))
    {κ : Type u} (n : ℕ)
    (f : κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal)
    (C : ENNReal)
    (hbound : ∀ i, (μs i : Measure VagueRationalWindowState)
      (smoothedClosePairEvent n f) ≤ C) :
    (μ : Measure VagueRationalWindowState)
      (smoothedClosePairEvent n f) ≤ C := by
  exact measure_open_le_of_tendsto_of_forall_le hlim
    (isOpen_smoothedClosePairEvent n f) hbound

/-- The paper's collision-exclusion argument specialized to smoothed local
test events.  Once the finite-volume close-pair estimate is established for
the chosen bump family at every positive resolution, no further topological
hypothesis is needed. -/
theorem measure_localMultiplicityCollisionEvent_eq_zero
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {α : Type*} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (hlim : Tendsto μs L (𝓝 μ))
    {κ : Type u} (n : ℕ)
    (f : ℝ → κ → BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal)
    (hcover : ∀ a, 0 < a → ∀ x : MarkedSpectralSpace Unit,
      ∃ k, f a k x = 1)
    (scale : ℕ → ℝ) {R K : ℝ}
    (hscale_pos : ∀ m, 0 < scale m)
    (hscale_zero : Tendsto scale atTop (𝓝 0))
    (hbound : ∀ m i,
      (μs i : Measure VagueRationalWindowState)
          (smoothedClosePairEvent n (f (scale m))) ≤
        ENNReal.ofReal
          (8 * K ^ 2 * R * scale m + 16 * K ^ 2 * (scale m) ^ 2)) :
    (μ : Measure VagueRationalWindowState)
      (localMultiplicityCollisionEvent n) = 0 := by
  apply measure_limitCollision_eq_zero hlim
    (fun a => smoothedClosePairEvent n (f a))
    (localMultiplicityCollisionEvent n)
    (fun a _ => isOpen_smoothedClosePairEvent n (f a))
    (fun a ha =>
      localMultiplicityCollisionEvent_subset_smoothedClosePairEvent
        n (f a) (hcover a ha))
    scale hscale_pos hscale_zero
  exact hbound

end CoareaNative.BlockBand
