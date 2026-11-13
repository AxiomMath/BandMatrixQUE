module

public import BlockBand.SourceProcess.SourcePins.AtomSet

/-!
# Identification of the measures in `atomSet` (`EntranceAtomic`)

* `restrict_ppos_eq`: two finite measures on `[0,1]` that agree on every bounded continuous test
  vanishing on some `[0,x]`, `x > 0`, agree on `(0,1]`. The tests `g χ_n`, with
  `χ_n(y) = min 1 (max 0 ((n+1)y − 1))`, converge boundedly to `g 1_{(0,1]}`.
* `exists_seq_of_mem_atomSet`: a measure in `atomSet p R` (`0 < p ≤ 1`) without mass at `0` is
  `seqTraceMeasure t` for a transmission sequence `t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The cutoff `χ_n(y) = min 1 (max 0 ((n+1)y − 1))`. -/
def cutoffFn (n : ℕ) (y : unitInterval) : ℝ := min 1 (max 0 (((n : ℝ) + 1) * y - 1))

theorem continuous_cutoffFn (n : ℕ) : Continuous (cutoffFn n) :=
  continuous_const.min (continuous_const.max
    ((continuous_const.mul continuous_subtype_val).sub continuous_const))

theorem cutoffFn_mem (n : ℕ) (y : unitInterval) : 0 ≤ cutoffFn n y ∧ cutoffFn n y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem cutoffFn_eq_zero {n : ℕ} {y : unitInterval} (hy : (y : ℝ) ≤ 1 / ((n : ℝ) + 1)) :
    cutoffFn n y = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : ((n : ℝ) + 1) * y ≤ 1 := by rwa [le_div_iff₀ hn, mul_comm] at hy
  simp only [cutoffFn]
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem tendsto_cutoffFn (y : unitInterval) :
    Tendsto (fun n => cutoffFn n y) atTop (𝓝 (ppos.indicator 1 y)) := by
  by_cases hy : y ∈ ppos
  · rw [indicator_of_mem hy]
    have hy' : (0 : ℝ) < y := hy
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (y : ℝ))
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    have h1 : (2 : ℝ) < N * y := by rwa [div_lt_iff₀ hy'] at hN
    have h2 : (N : ℝ) * y ≤ n * y := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hy'.le
    simp only [cutoffFn, Pi.one_apply]
    rw [min_eq_left (le_max_of_le_right (by nlinarith))]
  · rw [indicator_of_notMem hy]
    have hy0 : (y : ℝ) ≤ 0 := not_lt.1 hy
    exact tendsto_const_nhds.congr fun n =>
      (cutoffFn_eq_zero (hy0.trans (by positivity))).symm

/-- The test `g χ_n`. -/
def cutBCF (g : unitInterval →ᵇ ℝ) (n : ℕ) : unitInterval →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => g y * cutoffFn n y, g.continuous.mul (continuous_cutoffFn n)⟩

theorem cutBCF_apply (g : unitInterval →ᵇ ℝ) (n : ℕ) (y : unitInterval) :
    cutBCF g n y = g y * cutoffFn n y := rfl

theorem tendsto_integral_cutBCF (ν : Measure unitInterval) [IsFiniteMeasure ν]
    (g : unitInterval →ᵇ ℝ) :
    Tendsto (fun n => ∫ y, cutBCF g n y ∂ν) atTop (𝓝 (∫ y, g y ∂(ν.restrict ppos))) := by
  rw [← integral_indicator measurableSet_ppos]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
    (fun n => (cutBCF g n).continuous.aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
  · rw [cutBCF_apply, norm_mul]
    have h1 := cutoffFn_mem n y
    have h2 : ‖cutoffFn n y‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h1.1]; exact h1.2
    calc ‖g y‖ * ‖cutoffFn n y‖ ≤ ‖g‖ * 1 :=
          mul_le_mul (g.norm_coe_le_norm y) h2 (norm_nonneg _) (norm_nonneg _)
      _ = ‖g‖ := mul_one _
  · have := (tendsto_const_nhds (x := g y)).mul (tendsto_cutoffFn y)
    have he : ppos.indicator (fun y => g y) y = g y * ppos.indicator 1 y := by
      by_cases hy : y ∈ ppos
      · rw [indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, mul_one]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
    rw [he]
    exact this

/-- **Agreement on `(0,1]`.** -/
theorem restrict_ppos_eq {ν₁ ν₂ : Measure unitInterval} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ x : ℝ, 0 < x → ∀ f : unitInterval →ᵇ ℝ, (∀ y : unitInterval, (y : ℝ) ≤ x → f y = 0) →
      ∫ y, f y ∂ν₁ = ∫ y, f y ∂ν₂) : ν₁.restrict ppos = ν₂.restrict ppos := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  refine tendsto_nhds_unique (tendsto_integral_cutBCF ν₁ g) ?_
  refine (tendsto_integral_cutBCF ν₂ g).congr fun n =>
    (h (1 / ((n : ℝ) + 1)) (by positivity) _ fun y hy => ?_).symm
  rw [cutBCF_apply, cutoffFn_eq_zero hy, mul_zero]

theorem ppos_compl : pposᶜ = ({0} : Set unitInterval) := by
  ext y
  simp only [ppos, mem_compl_iff, mem_ofPred_eq, not_lt, mem_singleton_iff]
  constructor
  · intro h; exact Subtype.ext (le_antisymm h y.2.1)
  · rintro rfl; simp

/-- **A measure of `atomSet` without mass at `0` is the trace measure of a transmission
sequence.** -/
theorem exists_seq_of_mem_atomSet {p R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {ν : FiniteMeasure unitInterval} (hν : ν ∈ atomSet p R)
    (h0 : (ν : Measure unitInterval) {0} = 0) :
    ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧ (ν : Measure unitInterval) = seqTraceMeasure t := by
  obtain ⟨t, ht, hag⟩ := hν
  have ht0 : ∀ i, 0 ≤ t i := fun i => (ht.2.1 i).1
  have hs := summable_of_pBound hp1 ht
  have := isFiniteMeasure_seqTraceMeasure ht0 hs
  refine ⟨t, ⟨ht.1, ht.2.1, hs⟩, ?_⟩
  have hres := restrict_ppos_eq (ν₁ := (ν : Measure unitInterval)) (ν₂ := seqTraceMeasure t)
    fun x hx f hf => by rw [hag x hx f hf, integral_seqTraceMeasure_cut hp hp1 hx ht f hf]
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := (ν : Measure unitInterval))
    measurableSet_ppos]
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := seqTraceMeasure t)
    measurableSet_ppos]
  rw [hres, ppos_compl, Measure.restrict_eq_zero.2 h0,
    Measure.restrict_eq_zero.2 (seqTraceMeasure_zero ht0)]

end BlockBand.SourceProcess.SourcePins
