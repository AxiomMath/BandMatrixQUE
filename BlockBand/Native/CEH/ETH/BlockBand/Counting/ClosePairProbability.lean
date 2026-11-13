module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.ClosePairGrid
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Probability consequences of the close-pair estimate

This module records the first-moment/Markov consequence of the deterministic
real-line grid estimate used for the close-pair estimate.  For a finite random point configuration, the probability of an
ordered close pair in `[-R,R]` is bounded by

`8 K^2 R a + 16 K^2 a^2`.

The final theorems give a finite-level collision exclusion: close-pair
probabilities vanish along any positive scale tending to zero, and uniform
control at all such scales excludes exact collisions for a fixed finite
configuration.  Passing either statement to a subsequential point-process
limit would require an explicit convergence interface (for example a
suitable Portmanteau theorem) and is not asserted here.  All finite-dimensional
integrability, window-moment, positivity, and limit assumptions are explicit
hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory Filter
open scoped Topology

/-- Event that a finite point configuration contains an ordered distinct pair
in `[-R,R]` at distance strictly less than `a`. -/
def closePairEvent
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Ω → ι → ℝ) (R a : ℝ) : Set Ω :=
  {ω | (closePairIndices (u ω) R a).Nonempty}

/-- Event that two distinct indexed points coincide inside `[-R,R]`.
This is the finite-configuration collision event whose exclusion is needed
before identifying a subsequential limit as a simple point process. -/
def exactCollisionEvent
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Ω → ι → ℝ) (R : ℝ) : Set Ω :=
  {ω | ∃ ij ∈ orderedDistinctPairs (Finset.univ : Finset ι),
    |u ω ij.1| ≤ R ∧ |u ω ij.2| ≤ R ∧ u ω ij.1 = u ω ij.2}

/-- An exact collision is a close pair at every strictly positive scale. -/
theorem exactCollisionEvent_subset_closePairEvent
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Ω → ι → ℝ) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    exactCollisionEvent u R ⊆ closePairEvent u R a := by
  intro ω hω
  rcases hω with ⟨ij, hij, hiR, hjR, heq⟩
  refine ⟨ij, ?_⟩
  simp only [closePairIndices, Finset.mem_filter]
  refine ⟨hij, hiR, hjR, ?_⟩
  rw [heq, sub_self, abs_zero]
  exact ha

/-- Markov's inequality combined with the grid-window factorial moment bound.
This is the probability form of the close-pair estimate, with its exact
constants and with no probability-space normalization hidden in the proof. -/
theorem measure_closePairEvent_le_manuscript
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (u : Ω → ι → ℝ)
    {R a K : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hpairInt : Integrable
      (fun ω => ((closePairIndices (u ω) R a).card : ℝ)) μ)
    (hwindowInt : ∀ j : Fin (closePairGridSize R a),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ)) μ)
    (hmoment : ∀ j : Fin (closePairGridSize R a),
      ∫ ω, ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ) ∂μ
        ≤ (2 * K * a) ^ 2) :
    μ (closePairEvent u R a) ≤
      ENNReal.ofReal (8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2) := by
  have hmarkov : μ (closePairEvent u R a) ≤
      ENNReal.ofReal
        (∫ ω, ((closePairIndices (u ω) R a).card : ℝ) ∂μ) := by
    apply hpairInt.measure_le_integral
    · exact Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _
    · intro ω hω
      exact_mod_cast Finset.card_pos.mpr hω
  exact hmarkov.trans (ENNReal.ofReal_le_ofReal
    (integral_closePairIndices_le_manuscript μ u hR ha
      hpairInt hwindowInt hmoment))

/-- Any bad event contained in the close-pair event inherits the same exact
probability bound. No limit-law assertion is built into it. -/
theorem measure_badEvent_le_of_subset_closePairEvent
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (u : Ω → ι → ℝ) (bad : Set Ω)
    {R a K : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hbad : bad ⊆ closePairEvent u R a)
    (hpairInt : Integrable
      (fun ω => ((closePairIndices (u ω) R a).card : ℝ)) μ)
    (hwindowInt : ∀ j : Fin (closePairGridSize R a),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ)) μ)
    (hmoment : ∀ j : Fin (closePairGridSize R a),
      ∫ ω, ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ) ∂μ
        ≤ (2 * K * a) ^ 2) :
    μ bad ≤ ENNReal.ofReal
      (8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2) := by
  exact (measure_mono hbad).trans
    (measure_closePairEvent_le_manuscript μ u hR ha
      hpairInt hwindowInt hmoment)

/-- At every positive resolution, the exact collision event inherits the
same close-pair probability bound.  Letting the resolution tend
to zero can therefore exclude collisions once the window hypotheses are
available uniformly along that limiting operation. -/
theorem measure_exactCollisionEvent_le_manuscript
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (u : Ω → ι → ℝ)
    {R a K : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hpairInt : Integrable
      (fun ω => ((closePairIndices (u ω) R a).card : ℝ)) μ)
    (hwindowInt : ∀ j : Fin (closePairGridSize R a),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ)) μ)
    (hmoment : ∀ j : Fin (closePairGridSize R a),
      ∫ ω, ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ) ∂μ
        ≤ (2 * K * a) ^ 2) :
    μ (exactCollisionEvent u R) ≤ ENNReal.ofReal
      (8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2) := by
  exact measure_badEvent_le_of_subset_closePairEvent μ u
    (exactCollisionEvent u R) hR ha
    (exactCollisionEvent_subset_closePairEvent u R ha)
    hpairInt hwindowInt hmoment

/-- The explicit right-hand side tends to zero whenever the
positive close-pair scale tends to zero. -/
theorem tendsto_closePair_manuscript_bound_zero
    {α : Type*} {l : Filter α} (a : α → ℝ) (R K : ℝ)
    (ha : Tendsto a l (𝓝 0)) :
    Tendsto
      (fun n => ENNReal.ofReal
        (8 * K ^ 2 * R * a n + 16 * K ^ 2 * (a n) ^ 2))
      l (𝓝 0) := by
  have hreal : Tendsto
      (fun n => 8 * K ^ 2 * R * a n + 16 * K ^ 2 * (a n) ^ 2)
      l (𝓝 0) := by
    simpa using (ha.const_mul (8 * K ^ 2 * R)).add
      ((ha.pow 2).const_mul (16 * K ^ 2))
  have hofReal : Tendsto
      (ENNReal.ofReal ∘
        fun n => 8 * K ^ 2 * R * a n + 16 * K ^ 2 * (a n) ^ 2)
      l (𝓝 (ENNReal.ofReal 0)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [ENNReal.ofReal_zero] at hofReal
  exact hofReal.congr' (Filter.Eventually.of_forall fun _ => rfl)

/-- Collision exclusion for a varying family of finite random point
configurations.  Uniform grid-window factorial bounds imply that the
probability of a close pair in the fixed compact interval `[-R,R]` vanishes
at every positive scale `a n → 0`.  The measures and configurations may vary
with `n`; tightness and transfer to a subsequential point-process law are
not part of this statement. -/
theorem tendsto_measure_closePairEvent_zero
    {α Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {l : Filter α} (μ : α → Measure Ω) (u : α → Ω → ι → ℝ)
    (a : α → ℝ) {R K : ℝ} (hR : 0 ≤ R)
    (ha_pos : ∀ n, 0 < a n) (ha_zero : Tendsto a l (𝓝 0))
    (hpairInt : ∀ n, Integrable
      (fun ω => ((closePairIndices (u n ω) R (a n)).card : ℝ)) (μ n))
    (hwindowInt : ∀ n (j : Fin (closePairGridSize R (a n))),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u n ω) R (a n) j).card.descFactorial 2 : ℝ))
        (μ n))
    (hmoment : ∀ n (j : Fin (closePairGridSize R (a n))),
      ∫ ω,
          ((closePairGridWindow (u n ω) R (a n) j).card.descFactorial 2 : ℝ)
        ∂μ n ≤ (2 * K * a n) ^ 2) :
    Tendsto (fun n => μ n (closePairEvent (u n) R (a n))) l (𝓝 0) := by
  have hzero : Tendsto (fun _ : α => (0 : ENNReal)) l (𝓝 0) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hzero
    (tendsto_closePair_manuscript_bound_zero a R K ha_zero)
  · intro n
    exact bot_le
  · intro n
    exact measure_closePairEvent_le_manuscript (μ n) (u n) hR (ha_pos n)
      (hpairInt n) (hwindowInt n) (hmoment n)

/-- For one finite random point configuration, factorial-window control at
arbitrarily small positive scales excludes exact collisions in `[-R,R]`.
This is a finite-level simplicity statement.  Applying it to a subsequential
point-process limit would require hypotheses connecting the limiting law's
collision event to these finite-level events. -/
theorem measure_exactCollisionEvent_eq_zero_of_uniform_scales
    {α Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {l : Filter α} [NeBot l] (μ : Measure Ω) (u : Ω → ι → ℝ)
    (a : α → ℝ) {R K : ℝ} (hR : 0 ≤ R)
    (ha_pos : ∀ n, 0 < a n) (ha_zero : Tendsto a l (𝓝 0))
    (hpairInt : ∀ n, Integrable
      (fun ω => ((closePairIndices (u ω) R (a n)).card : ℝ)) μ)
    (hwindowInt : ∀ n (j : Fin (closePairGridSize R (a n))),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u ω) R (a n) j).card.descFactorial 2 : ℝ))
        μ)
    (hmoment : ∀ n (j : Fin (closePairGridSize R (a n))),
      ∫ ω,
          ((closePairGridWindow (u ω) R (a n) j).card.descFactorial 2 : ℝ)
        ∂μ ≤ (2 * K * a n) ^ 2) :
    μ (exactCollisionEvent u R) = 0 := by
  have hclose : Tendsto
      (fun n => μ (closePairEvent u R (a n))) l (𝓝 0) :=
    tendsto_measure_closePairEvent_zero
      (fun _ => μ) (fun _ => u) a hR ha_pos ha_zero
      hpairInt hwindowInt hmoment
  have hcollision : Tendsto
      (fun _ : α => μ (exactCollisionEvent u R)) l (𝓝 0) := by
    have hzero : Tendsto (fun _ : α => (0 : ENNReal)) l (𝓝 0) :=
      tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hclose
    · intro n
      exact bot_le
    · intro n
      exact measure_mono
        (exactCollisionEvent_subset_closePairEvent u R (ha_pos n))
  exact tendsto_nhds_unique tendsto_const_nhds hcollision

end CEHNative.BlockBand
