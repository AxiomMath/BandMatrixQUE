module

public import BlockBand.SourceProcess.SourceProcessLaw.Extraction

/-!
# Continuous counting tests for the cap event

The cap set `capSet K h = {t_K ≤ h²}` is not a continuity set of the weak topology. It is sandwiched
between continuous tests. For thresholds `0 < a < c` the weight
`cutWeight a c y = min(1, max(0, (y - a)/(c - a))) / max(y, a)` lies between the count weights
`1{y ≥ c}/y` and `1{y ≥ a}/y`. On a trace measure `ν = Σ_i t_i δ_{t_i}` of a transmission sequence:
* `t_K < a ⟹ ∫ cutWeight dν ≤ K` (`integral_cutWeight_le`);
* `∫ cutWeight dν < K + 1 ⟹ t_K < c` (`lt_of_integral_cutWeight_lt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal

/-- The continuous count weight between the thresholds `a < c`. -/
def cutWeight (a c : ℝ) (y : unitInterval) : ℝ :=
  min 1 (max 0 (((y : ℝ) - a) / (c - a))) / max (y : ℝ) a

theorem cutWeight_nonneg (a c : ℝ) (y : unitInterval) : 0 ≤ cutWeight a c y := by
  unfold cutWeight
  rcases le_total 0 a with ha | ha
  · exact div_nonneg (le_min zero_le_one (le_max_left _ _)) (ha.trans (le_max_right _ _))
  · exact div_nonneg (le_min zero_le_one (le_max_left _ _)) (y.2.1.trans (le_max_left _ _))

theorem continuous_cutWeight {a : ℝ} (ha : 0 < a) (c : ℝ) : Continuous (cutWeight a c) := by
  unfold cutWeight
  refine Continuous.div (continuous_const.min (continuous_const.max
    ((continuous_subtype_val.sub continuous_const).div_const _)))
    (continuous_subtype_val.max continuous_const) fun y => ?_
  exact (ha.trans_le (le_max_right _ _)).ne'

theorem countWeight_le_cutWeight {a c : ℝ} (hac : a < c) (y : unitInterval) :
    countWeight c y ≤ ENNReal.ofReal (cutWeight a c y) := by
  unfold countWeight
  by_cases hy : c ≤ (y : ℝ)
  · rw [Set.indicator_of_mem (show y ∈ {y : unitInterval | c ≤ (y : ℝ)} from hy)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have h1 : 1 ≤ ((y : ℝ) - a) / (c - a) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    unfold cutWeight
    rw [max_eq_right (by linarith), min_eq_left h1, max_eq_left (by linarith)]
  · rw [Set.indicator_of_notMem (show y ∉ {y : unitInterval | c ≤ (y : ℝ)} from hy)]
    exact bot_le

theorem cutWeight_le_countWeight {a c : ℝ} (ha : 0 < a) (hac : a < c) (y : unitInterval) :
    ENNReal.ofReal (cutWeight a c y) ≤ countWeight a y := by
  unfold countWeight
  by_cases hy : a ≤ (y : ℝ)
  · rw [Set.indicator_of_mem (show y ∈ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cutWeight
    rw [max_eq_left hy]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (ha.trans_le hy).le
  · rw [Set.indicator_of_notMem (show y ∉ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
    have : max 0 (((y : ℝ) - a) / (c - a)) = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    simp [cutWeight, this]

/-- At most `K` atoms above `x` when `t_K < x`. -/
theorem atomCount_le_of_lt {t : ℕ → ℝ} (ht : IsTransmissionSequence t) {x : ℝ} (hx : 0 < x)
    {K : ℕ} (hK : t K < x) : atomCount x (seqTraceMeasure t) ≤ K := by
  rw [atomCount_seqTraceMeasure ht hx]
  have hzero : ∀ j ∉ Finset.range K, (if x ≤ t j then (1 : ℝ≥0∞) else 0) = 0 := by
    intro j hj
    have hij : K ≤ j := by simpa using hj
    rw [ite_eq_right_iff]
    intro hxj
    exact absurd ((ht.1 hij).trans_lt hK) (not_lt.2 hxj)
  rw [tsum_eq_sum hzero]
  calc (∑ j ∈ Finset.range K, if x ≤ t j then (1 : ℝ≥0∞) else 0)
      ≤ ∑ _j ∈ Finset.range K, (1 : ℝ≥0∞) := Finset.sum_le_sum fun j _ => by split_ifs <;> simp
    _ = K := by simp

theorem lt_of_atomCount_lt {t : ℕ → ℝ} (ht : IsTransmissionSequence t) {x : ℝ} (hx : 0 < x)
    {K : ℕ} (hK : atomCount x (seqTraceMeasure t) < ((K + 1 : ℕ) : ℝ≥0∞)) : t K < x := by
  rw [atomCount_seqTraceMeasure ht hx] at hK
  by_contra hle
  exact absurd ((count_ge_iff ht.1 x K).2 (not_lt.1 hle)) (not_le.2 hK)

theorem integral_cutWeight_eq (ν : FiniteMeasure unitInterval) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ y, cutWeight a c y ∂(ν : Measure unitInterval) =
      (∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval)).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (cutWeight_nonneg a c))
    (continuous_cutWeight ha c).aestronglyMeasurable

/-- **Upper count**: `t_K < a ⟹ ∫ cutWeight dν ≤ K`. -/
theorem integral_cutWeight_le (ν : FiniteMeasure unitInterval) {t : ℕ → ℝ}
    (hν : (ν : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) {K : ℕ} (hK : t K < a) :
    ∫ y, cutWeight a c y ∂(ν : Measure unitInterval) ≤ K := by
  have hle : ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval) ≤ K := by
    calc ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval)
        ≤ atomCount a (ν : Measure unitInterval) :=
          lintegral_mono fun y => cutWeight_le_countWeight ha hac y
      _ ≤ K := by rw [hν]; exact atomCount_le_of_lt ht ha hK
  rw [integral_cutWeight_eq ν ha c]
  simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top K) hle

/-- **Lower count**: `∫ cutWeight dν < K + 1 ⟹ t_K < c`. -/
theorem lt_of_integral_cutWeight_lt (ν : FiniteMeasure unitInterval) {t : ℕ → ℝ}
    (hν : (ν : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) {K : ℕ}
    (hK : ∫ y, cutWeight a c y ∂(ν : Measure unitInterval) < K + 1) : t K < c := by
  refine lt_of_atomCount_lt ht (ha.trans hac) ?_
  have hfin : ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval) ≠ ∞ := by
    have hb : ∀ y, ENNReal.ofReal (cutWeight a c y) ≤ ENNReal.ofReal (1 / a) := fun y =>
      (cutWeight_le_countWeight ha hac y).trans (by
        unfold countWeight
        by_cases hy : a ≤ (y : ℝ)
        · rw [Set.indicator_of_mem (show y ∈ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
          exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ha hy)
        · rw [Set.indicator_of_notMem (show y ∉ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
          exact bot_le)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [integral_cutWeight_eq ν ha c] at hK
  have hK' : ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval) <
      ((K + 1 : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hfin, show ((K + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hK
  rw [← hν]
  calc atomCount c (ν : Measure unitInterval)
      ≤ ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval) :=
        lintegral_mono fun y => countWeight_le_cutWeight hac y
    _ < _ := hK'

end BlockBand.SourceProcess.CapCond
