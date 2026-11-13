module

public import BlockBand.SourceProcess.CapCond.Test
public import BlockBand.SourceProcess.ClosedIdent.Restrict

/-!
# The cap probability against the cap test, at finite width and in the limit

Write `A_W = physCapEvent = {μ_W(s) ∈ capSet K h}` and `t_K(ν) = seqExtract ν K`.
* `capProb_le_integral` (`h² < a < c`): `P_W(A_W) ≤ E_W capTest a c K (μ_W(s))`.
* `integral_le_capProb` (`a < c ≤ h²`): `E_W capTest a c K (μ_W(s)) ≤ P_W(A_W)`.
* `integral_capTest_le` (`a < c`): `E capTest a c K (μ(s)) ≤ P(t_K(μ(s)) < c)`.
* `le_integral_capTest` (`a < c`): `P(t_K(μ(s)) < a) ≤ E capTest a c K (μ(s))`.
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

variable {b E : ℝ} {W : ℕ}

/-- `P_W(A_W)` as the integral of the indicator of the Borel version of the event. -/
theorem capProb_eq_integral (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ) (K : ℕ) :
    (growthPathLaw W b (physCapEvent b E s h K W)).toReal =
      ∫ ω, (physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) ω ∂growthPathLaw W b := by
  have e3 := integral_indicator_one (μ := growthPathLaw W b) (measurableSet_physCapEventM b E s h K W)
  rw [Pi.one_def] at e3
  rw [e3, measureReal_def, measure_congr (physCapEvent_ae_eq hb hE1 hE2 s h K)]

theorem integrable_capIndicator (b E s h : ℝ) (K : ℕ) :
    Integrable (fun ω => (physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) ω)
      (growthPathLaw W b) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_physCapEventM b E s h K W)

/-- **Finite width, upper side** (`h² < a < c`). -/
theorem capProb_le_integral (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    {s h a c : ℝ} (ha : 0 < a) (hac : a < c) (hha : h ^ 2 < a) (K : ℕ) :
    (growthPathLaw W b (physCapEvent b E s h K W)).toReal ≤
      ∫ ω, capTest a c ha K (fun _ => transmissionProcess b E (fun _ => 0) W s ω)
        ∂growthPathLaw W b := by
  rw [capProb_eq_integral (by linarith) hE1 hE2 s h K]
  refine integral_mono_ae (integrable_capIndicator b E s h K)
    (integrable_capTest_W hb hE1 hE2 s a c ha K) ?_
  filter_upwards [ae_transmissionProcess_seq hb hE1 hE2 hW s,
    (physCapEvent_ae_eq (b := b) (W := W) (by linarith) hE1 hE2 s h K).mem_iff] with ω hω hmem
  by_cases hM : ω ∈ physCapEventM b E s h K W
  · rw [Set.indicator_of_mem hM]
    have hA : ω ∈ physCapEvent b E s h K W := hmem.2 hM
    change seqExtract _ K ≤ h ^ 2 at hA
    rw [hω.2, seqExtract_seqTraceMeasure hω.1] at hA
    exact (capTest_eq_one ha hac hω.2 hω.1 (hA.trans_lt hha)).ge
  · rw [Set.indicator_of_notMem hM]
    exact capTest_nonneg _ _ _ _ _

/-- **Finite width, lower side** (`a < c ≤ h²`). -/
theorem integral_le_capProb (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    {s h a c : ℝ} (ha : 0 < a) (hac : a < c) (hch : c ≤ h ^ 2) (K : ℕ) :
    ∫ ω, capTest a c ha K (fun _ => transmissionProcess b E (fun _ => 0) W s ω)
        ∂growthPathLaw W b ≤ (growthPathLaw W b (physCapEvent b E s h K W)).toReal := by
  rw [capProb_eq_integral (by linarith) hE1 hE2 s h K]
  refine integral_mono_ae (integrable_capTest_W hb hE1 hE2 s a c ha K)
    (integrable_capIndicator b E s h K) ?_
  filter_upwards [ae_transmissionProcess_seq hb hE1 hE2 hW s,
    (physCapEvent_ae_eq (b := b) (W := W) (by linarith) hE1 hE2 s h K).mem_iff] with ω hω hmem
  rcases (capTest_nonneg a c ha K (fun _ => transmissionProcess b E (fun _ => 0) W s ω)).lt_or_eq
    with hpos | hz
  · have hlt := lt_of_capTest_pos ha hac hω.2 hω.1 hpos
    have hA : ω ∈ physCapEvent b E s h K W := by
      change seqExtract _ K ≤ h ^ 2
      rw [hω.2, seqExtract_seqTraceMeasure hω.1]
      exact (hlt.trans_le hch).le
    rw [Set.indicator_of_mem (hmem.1 hA)]
    exact capTest_le_one _ _ _ _ _
  · change capTest a c ha K _ ≤ _
    rw [← hz]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

section Limit

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}

theorem entranceProb_eq_integral [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    (entranceLaw P μ s S).toReal =
      ∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ S}.indicator (fun _ => (1 : ℝ)) ω ∂P := by
  have hm : MeasurableSet {ω | (μ s ω : Measure unitInterval) ∈ S} :=
    (measurable_subtype_coe.comp hμ) hS
  have e3 := integral_indicator_one (μ := P) hm
  rw [Pi.one_def] at e3
  rw [e3, measureReal_def, entranceLaw_apply P hμ hS]

theorem integrable_entranceIndicator [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    Integrable (fun ω => {ω | (μ s ω : Measure unitInterval) ∈ S}.indicator (fun _ => (1 : ℝ)) ω)
      P :=
  (integrable_const (1 : ℝ)).indicator ((measurable_subtype_coe.comp hμ) hS)

/-- **Limit, upper side** (`a < c`): `E capTest(μ(s)) ≤ P(t_K(μ(s)) < c)`, given a.s. atomicity. -/
theorem integral_capTest_le [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    (hA : ∀ᵐ ω ∂P, ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧
      (μ s ω : Measure unitInterval) = seqTraceMeasure t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) (K : ℕ) :
    ∫ ω, capTest a c ha K (fun _ => μ s ω) ∂P ≤
      (entranceLaw P μ s {ν | seqExtract ν K < c}).toReal := by
  rw [entranceProb_eq_integral hμ (measurableSet_extract_lt K c)]
  refine integral_mono_ae (integrable_capTest_lim hμ a c ha K)
    (integrable_entranceIndicator hμ (measurableSet_extract_lt K c)) ?_
  filter_upwards [hA] with ω ⟨t, ht, hν⟩
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rcases (capTest_nonneg a c ha K (fun _ => μ s ω)).lt_or_eq with hpos | hz
  · have hlt := lt_of_capTest_pos ha hac hν ht hpos
    have hmem : seqExtract (μ s ω : Measure unitInterval) K < c := by
      rw [hν, seqExtract_seqTraceMeasure ht]
      exact hlt
    rw [ite_eq_left hmem]
    exact capTest_le_one _ _ _ _ _
  · rw [← hz]
    split_ifs <;> norm_num

/-- **Limit, lower side** (`a < c`): `P(t_K(μ(s)) < a) ≤ E capTest(μ(s))`, given a.s. atomicity. -/
theorem le_integral_capTest [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    (hA : ∀ᵐ ω ∂P, ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧
      (μ s ω : Measure unitInterval) = seqTraceMeasure t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) (K : ℕ) :
    (entranceLaw P μ s {ν | seqExtract ν K < a}).toReal ≤
      ∫ ω, capTest a c ha K (fun _ => μ s ω) ∂P := by
  rw [entranceProb_eq_integral hμ (measurableSet_extract_lt K a)]
  refine integral_mono_ae (integrable_entranceIndicator hμ (measurableSet_extract_lt K a))
    (integrable_capTest_lim hμ a c ha K) ?_
  filter_upwards [hA] with ω ⟨t, ht, hν⟩
  simp only [Set.indicator, Set.mem_ofPred_eq]
  split_ifs with hmem
  · have hlt : t K < a := by rwa [hν, seqExtract_seqTraceMeasure ht] at hmem
    exact (capTest_eq_one ha hac hν ht hlt).ge
  · exact capTest_nonneg _ _ _ _ _

end Limit

end BlockBand.SourceProcess.CapCond
