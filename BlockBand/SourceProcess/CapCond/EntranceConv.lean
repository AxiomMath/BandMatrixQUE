module

public import BlockBand.SourceProcess.CapCond.EntranceLim

/-!
# Sandwich bounds for the weighted entrance on the cap event

These bounds are used to prove `tendsto_capWeighted`. The cap indicator is sandwiched between the
weighted tests `wTest` with thresholds above `h²` (upper bound) and below `h²` (lower bound); each
test passes to the limit with `IsTransmissionLimit.fdd` at the single time `s`, and the gaps are
closed with `limInt_sub_le`, continuity of the entrance law in the threshold, and the absence of an
atom of `t_K(μ(s))` at `h²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosedPath
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E : ℝ} {w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ}

/-- Finite width, upper (`h² < a < c`). -/
theorem finInt_le (hw : ∀ ν, 0 ≤ w ν) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    (hW : 1 ≤ W) {s h a c : ℝ} (ha : 0 < a) (hac : a < c) (hha : h ^ 2 < a) (K : ℕ) :
    finInt b E s h K W w ≤
      ∫ ω, wTest a c ha K w (fun _ => transmissionProcess b E (fun _ => 0) W s ω)
        ∂growthPathLaw W b := by
  refine integral_mono_ae (integrable_finInd hb hE1 hE2 s h K)
    (integrable_wTest_W hb hE1 hE2 s a c ha K) ?_
  filter_upwards [ae_transmissionProcess_seq hb hE1 hE2 hW s,
    (physCapEvent_ae_eq (b := b) (W := W) (by linarith) hE1 hE2 s h K).mem_iff] with ω hω hmem
  have hB := wTest_bounds (v := fun _ => transmissionProcess b E (fun _ => 0) W s ω) hw ha hac K
    hω.2 hω.1
  by_cases hM : ω ∈ physCapEventM b E s h K W
  · rw [Set.indicator_of_mem hM]
    have hA : ω ∈ physCapEvent b E s h K W := hmem.2 hM
    change seqExtract _ K ≤ h ^ 2 at hA
    rw [hω.2, seqExtract_seqTraceMeasure hω.1] at hA
    exact hB.1 (hA.trans_lt hha)
  · rw [Set.indicator_of_notMem hM, wTest_apply]
    exact mul_nonneg (capTest_nonneg _ _ _ _ _) (hw _)

/-- Finite width, lower (`a < c ≤ h²`). -/
theorem le_finInt (hw : ∀ ν, 0 ≤ w ν) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    (hW : 1 ≤ W) {s h a c : ℝ} (ha : 0 < a) (hac : a < c) (hch : c ≤ h ^ 2) (K : ℕ) :
    ∫ ω, wTest a c ha K w (fun _ => transmissionProcess b E (fun _ => 0) W s ω)
        ∂growthPathLaw W b ≤ finInt b E s h K W w := by
  refine integral_mono_ae (integrable_wTest_W hb hE1 hE2 s a c ha K)
    (integrable_finInd hb hE1 hE2 s h K) ?_
  filter_upwards [ae_transmissionProcess_seq hb hE1 hE2 hW s,
    (physCapEvent_ae_eq (b := b) (W := W) (by linarith) hE1 hE2 s h K).mem_iff] with ω hω hmem
  refine (wTest_bounds (v := fun _ => transmissionProcess b E (fun _ => 0) W s ω) hw ha hac K
    hω.2 hω.1).2.trans ?_
  split_ifs with hlt
  · have hA : ω ∈ physCapEvent b E s h K W := by
      change seqExtract _ K ≤ h ^ 2
      rw [hω.2, seqExtract_seqTraceMeasure hω.1]
      exact (hlt.trans_le hch).le
    rw [Set.indicator_of_mem (hmem.1 hA)]
  · exact Set.indicator_nonneg (fun _ _ => hw _) _

variable [IsFiniteMeasure P] {s : ℝ}

/-- Limit, upper (`a < c`). -/
theorem integral_wTest_le (hw : ∀ ν, 0 ≤ w ν) (hμ : Measurable (μ s))
    (hA : ∀ᵐ ω ∂P, ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧
      (μ s ω : Measure unitInterval) = seqTraceMeasure t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) (K : ℕ) :
    ∫ ω, wTest a c ha K w (fun _ => μ s ω) ∂P ≤ limInt P μ s w {ν | seqExtract ν K < c} := by
  refine integral_mono_ae (integrable_wTest_lim hμ a c ha K)
    (integrable_limInd hμ (measurableSet_extract_lt K c)) ?_
  filter_upwards [hA] with ω ⟨t, ht, hν⟩
  refine (wTest_bounds (v := fun _ => μ s ω) hw ha hac K hν ht).2.trans (le_of_eq ?_)
  simp only [Set.indicator, Set.mem_ofPred_eq, hν, seqExtract_seqTraceMeasure ht]

/-- Limit, lower (`a < c`). -/
theorem limInt_le_integral_wTest (hw : ∀ ν, 0 ≤ w ν) (hμ : Measurable (μ s))
    (hA : ∀ᵐ ω ∂P, ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧
      (μ s ω : Measure unitInterval) = seqTraceMeasure t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) (K : ℕ) :
    limInt P μ s w {ν | seqExtract ν K < a} ≤ ∫ ω, wTest a c ha K w (fun _ => μ s ω) ∂P := by
  refine integral_mono_ae (integrable_limInd hμ (measurableSet_extract_lt K a))
    (integrable_wTest_lim hμ a c ha K) ?_
  filter_upwards [hA] with ω ⟨t, ht, hν⟩
  have hB := wTest_bounds (v := fun _ => μ s ω) hw ha hac K hν ht
  simp only [Set.indicator, Set.mem_ofPred_eq, hν, seqExtract_seqTraceMeasure ht]
  split_ifs with hlt
  · exact hB.1 hlt
  · rw [wTest_apply]; exact mul_nonneg (capTest_nonneg _ _ _ _ _) (hw _)

end BlockBand.SourceProcess.CapCond
