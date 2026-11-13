module

public import BlockBand.SourceProcess.SourceProcessLaw.Interface

/-!
# The entrance as the law of a random transmission sequence

`entrance_sequence`: under `EntranceAtomic` and `SeqExtraction`, the entrance law at a positive
time is the law of the trace measure of a random transmission sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory ProbabilityTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal

/-- The trace measure of a sequence depends measurably on the sequence (Giry σ-algebra). -/
theorem measurable_seqTraceMeasure : Measurable seqTraceMeasure := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hu : Measurable toUnit :=
    (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one)).measurable
  have : (fun t : ℕ → ℝ => seqTraceMeasure t A) =
      fun t => ∑' i, ENNReal.ofReal (t i) * A.indicator 1 (toUnit (t i)) := by
    funext t
    simp only [seqTraceMeasure, Measure.sum_apply _ hA, Measure.smul_apply,
      Measure.dirac_apply' _ hA, smul_eq_mul]
  rw [this]
  exact Measurable.tsum fun i => (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul
    ((measurable_one.indicator hA).comp (hu.comp (measurable_pi_apply i)))

theorem summable_iff_bdd {t : ℕ → ℝ} (h0 : ∀ i, 0 ≤ t i) :
    Summable t ↔ ∃ C : ℕ, ∀ N, ∑ i ∈ Finset.range N, t i ≤ C := by
  constructor
  · intro hs
    exact ⟨⌈∑' i, t i⌉₊, fun N => (hs.sum_le_tsum _ fun i _ => h0 i).trans (Nat.le_ceil _)⟩
  · rintro ⟨C, hC⟩
    exact summable_of_sum_range_le h0 hC

/-- The transmission sequences form a measurable set of sequences. -/
theorem measurableSet_transmissionSequence :
    MeasurableSet {t : ℕ → ℝ | IsTransmissionSequence t} := by
  have hset : {t : ℕ → ℝ | IsTransmissionSequence t} =
      (⋂ n : ℕ, {t : ℕ → ℝ | t (n + 1) ≤ t n}) ∩
        ((⋂ i : ℕ, {t : ℕ → ℝ | 0 ≤ t i} ∩ {t | t i ≤ 1}) ∩
          ⋃ C : ℕ, ⋂ N : ℕ, {t : ℕ → ℝ | ∑ i ∈ Finset.range N, t i ≤ C}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
      IsTransmissionSequence]
    constructor
    · rintro ⟨ha, hb, hs⟩
      exact ⟨fun n => ha (Nat.le_succ n), fun i => hb i,
        (summable_iff_bdd fun i => (hb i).1).1 hs⟩
    · rintro ⟨ha, hb, hs⟩
      exact ⟨antitone_nat_of_succ_le ha, hb, (summable_iff_bdd fun i => (hb i).1).2 hs⟩
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => ?_) (MeasurableSet.inter
    (MeasurableSet.iInter fun i => ?_) (MeasurableSet.iUnion fun C => MeasurableSet.iInter
      fun N => ?_))
  · exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
  · exact (measurableSet_le measurable_const (measurable_pi_apply _)).inter
      (measurableSet_le (measurable_pi_apply _) measurable_const)
  · exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      measurable_const

/-- **The entrance is the law of a random transmission sequence.** -/
theorem entrance_sequence (hA1 : EntranceAtomic) (hA2 : SeqExtraction) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hlim : IsTransmissionLimit b E (fun _ => 0) P μ)
    {s : ℝ} (hs : 0 < s) :
    ∃ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ ∧ (∀ᵐ t ∂ρ, IsTransmissionSequence t) ∧
      ρ.map seqTraceMeasure = entranceLaw P μ s := by
  obtain ⟨ext, hext, hinv⟩ := hA2
  have hat := hA1 b hb0 hb E hE1 hE2 Ω inferInstance P μ hlim s hs
  have hP := hlim.prob
  have hμ : Measurable fun ω => (μ s ω : Measure unitInterval) :=
    measurable_subtype_coe.comp (hlim.measurable s hs)
  have hf : Measurable fun ω => ext (μ s ω : Measure unitInterval) := hext.comp hμ
  refine ⟨P.map fun ω => ext (μ s ω : Measure unitInterval), inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hf.aemeasurable measurableSet_transmissionSequence]
    filter_upwards [hat] with ω ⟨t, ht, heq⟩
    rw [heq, hinv t ht]
    exact ht
  · rw [Measure.map_map measurable_seqTraceMeasure hf, entranceLaw]
    refine Measure.map_congr ?_
    filter_upwards [hat] with ω ⟨t, ht, heq⟩
    simp only [Function.comp_apply, heq, hinv t ht]

end BlockBand.SourceProcess.SourceProcessLaw
