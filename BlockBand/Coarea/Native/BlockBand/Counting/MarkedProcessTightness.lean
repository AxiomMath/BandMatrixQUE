module

public import BlockBand.Coarea.Native.BlockBand.Counting.ClosePairProbability
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite-window consequences for subsequential marked-process limits

All approximating and limiting laws live on one topological configuration
space `X`; the marks are part of `X`.  Weak convergence is represented by
`Tendsto` in Mathlib's `ProbabilityMeasure` topology.  Open finite-window
events are transferred by the open-set half of Portmanteau.  Consequently:

* uniform local-count tails exclude infinite mass in a fixed window;
* uniform close-pair estimates exclude collisions in that window; and
* any closed mark-validity condition holding almost surely before the limit
  still holds almost surely afterwards.

No Prokhorov theorem or existence of a convergent subsequence is asserted.
Those are separate tightness inputs.  The openness assumptions on count and
close-pair events are explicit because they depend on the eventual concrete
vague topology chosen for marked point measures.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology

/-- Open-set Portmanteau with a uniform upper bound.  This is the basic
finite-window transfer principle: although Portmanteau gives the limit law
below a `liminf`, a uniform bound on every approximating law also bounds that
`liminf`. -/
theorem measure_open_le_of_tendsto_of_forall_le
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {G : Set X} (hG : IsOpen G)
    {q : ENNReal} (hq : ∀ n, (μs n : Measure X) G ≤ q) :
    (μ : Measure X) G ≤ q := by
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG).trans ?_
  apply Filter.liminf_le_of_frequently_le'
  exact (Filter.Eventually.of_forall hq).frequently

/-- Quantitative local-count tail transfer to a weak subsequential limit.
The count is `ENNReal`-valued so that `∞` represents failure of
local finiteness in the chosen window. -/
theorem limit_localCount_tail_le
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (localCount : X → ENNReal)
    (hopen : ∀ m : ℕ, IsOpen {x | (m : ENNReal) ≤ localCount x})
    (C : ENNReal)
    (htail : ∀ n (m : ℕ), (μs n : Measure X)
      {x | (m : ENNReal) ≤ localCount x} ≤ C / (m : ENNReal))
    (m : ℕ) :
    (μ : Measure X) {x | (m : ENNReal) ≤ localCount x} ≤
      C / (m : ENNReal) := by
  exact measure_open_le_of_tendsto_of_forall_le hμ (hopen m)
    (fun n => htail n m)

/-- Uniform first-moment tails imply local finiteness of the weak limit in
one fixed spectral window.  Repeating this over a countable exhaustion of
`ℝ` is the remaining set-theoretic step for global local finiteness. -/
theorem measure_infiniteLocalCount_eq_zero
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (localCount : X → ENNReal)
    (hopen : ∀ m : ℕ, IsOpen {x | (m : ENNReal) ≤ localCount x})
    (C : ENNReal) (hC : C ≠ ⊤)
    (htail : ∀ n (m : ℕ), (μs n : Measure X)
      {x | (m : ENNReal) ≤ localCount x} ≤ C / (m : ENNReal)) :
    (μ : Measure X) {x | localCount x = ⊤} = 0 := by
  have hle : ∀ m : ℕ,
      (μ : Measure X) {x | localCount x = ⊤} ≤ C / (m : ENNReal) := by
    intro m
    apply (measure_mono ?_).trans
      (limit_localCount_tail_le hμ localCount hopen C htail m)
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hx]
    exact le_top
  have hdiv : Tendsto (fun m : ℕ => C / (m : ENNReal)) atTop (𝓝 0) :=
    by
      simpa [div_eq_mul_inv] using
        ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr hC)
  have hzero : Tendsto
      (fun _ : ℕ => (μ : Measure X) {x | localCount x = ⊤}) atTop (𝓝 0) := by
    have hz : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0) :=
      tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hz hdiv
    · intro m
      exact bot_le
    · exact hle
  exact tendsto_nhds_unique tendsto_const_nhds hzero

/-- Countably many finite-window conclusions combine into local finiteness
along an exhaustion.  A downstream marked-process model may take window `j`
to be `[-j,j] × 𝒫(𝕋)`. -/
theorem ae_localFinite_on_countable_exhaustion
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (localCount : ℕ → X → ENNReal)
    (hfinite : ∀ j, μ {x | localCount j x = ⊤} = 0) :
    ∀ᵐ x ∂μ, ∀ j, localCount j x ≠ ⊤ := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  simpa only [Classical.not_not] using hfinite j

/-- A uniform close-pair estimate transfers to any weak limit,
provided the corresponding finite-window close-pair event is open in the
chosen marked-configuration topology. -/
theorem limit_closePairEvent_le_manuscript
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (closePair : ℝ → Set X)
    (hopen : ∀ a, 0 < a → IsOpen (closePair a))
    {R K a : ℝ} (ha : 0 < a)
    (hbound : ∀ n, (μs n : Measure X) (closePair a) ≤
      ENNReal.ofReal (8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2)) :
    (μ : Measure X) (closePair a) ≤
      ENNReal.ofReal (8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2) := by
  exact measure_open_le_of_tendsto_of_forall_le hμ (hopen a ha) hbound

/-- Collision exclusion in a weak subsequential marked-process limit.  The
only topology-specific facts required are that every exact collision belongs
to every positive-resolution close-pair event and that those events are open.
The exact constants then vanish as `a ↓ 0`. -/
theorem measure_limitCollision_eq_zero
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ))
    (closePair : ℝ → Set X) (collision : Set X)
    (hopen : ∀ a, 0 < a → IsOpen (closePair a))
    (hcollision : ∀ a, 0 < a → collision ⊆ closePair a)
    (a : ℕ → ℝ) {R K : ℝ}
    (ha_pos : ∀ n, 0 < a n) (ha_zero : Tendsto a atTop (𝓝 0))
    (hbound : ∀ n i, (μs i : Measure X) (closePair (a n)) ≤
      ENNReal.ofReal
        (8 * K ^ 2 * R * a n + 16 * K ^ 2 * (a n) ^ 2)) :
    (μ : Measure X) collision = 0 := by
  have hle : ∀ n,
      (μ : Measure X) collision ≤ ENNReal.ofReal
        (8 * K ^ 2 * R * a n + 16 * K ^ 2 * (a n) ^ 2) := by
    intro n
    exact (measure_mono (hcollision (a n) (ha_pos n))).trans
      (limit_closePairEvent_le_manuscript hμ closePair hopen (ha_pos n)
        (hbound n))
  have hconst : Tendsto
      (fun _ : ℕ => (μ : Measure X) collision) atTop (𝓝 0) := by
    have hz : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0) :=
      tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hz
      (tendsto_closePair_manuscript_bound_zero a R K ha_zero)
    · intro n
      exact bot_le
    · exact hle
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- A closed mark-validity condition is preserved by a weak subsequential
limit.  In the paper this condition is that every mark lies in the
closed compact space `𝒫(𝕋)`: its complement is open and has zero probability
under every approximating marked law. -/
theorem measure_compl_closed_eq_zero_of_tendsto
    {X α : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter α} [NeBot l]
    {μ : ProbabilityMeasure X} {μs : α → ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (validMarks : Set X)
    (hclosed : IsClosed validMarks)
    (hvalid : ∀ n, (μs n : Measure X) validMarksᶜ = 0) :
    (μ : Measure X) validMarksᶜ = 0 := by
  exact le_antisymm
    (measure_open_le_of_tendsto_of_forall_le hμ hclosed.isOpen_compl
      (fun n => (hvalid n).le))
    bot_le

end CoareaNative.BlockBand
