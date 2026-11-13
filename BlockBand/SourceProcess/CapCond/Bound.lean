module

public import BlockBand.SourceProcess.CapCond.Atoms

/-!
# `0 ≤ cappedClosedTransform ≤ P_W(cap event)`

The closed integrand lies in `[0,1]` (`closedIntegrand_mem`), so the capped transform lies
between `0` and the probability of the physical cap event.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.Closing
open BlockBand.Transmission.Bridge BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {b E s T h : ℝ} {p J : ℕ} {q : Fin p → ℝ → ℝ} {a : Fin J → Fin p → ℝ} {K M W : ℕ}

/-- The integral over the sampled path law of a path-coordinate indicator. -/
theorem integral_pathIndicator (hq : ∀ i x, 0 ≤ q i x) {S : Set (GrowthPath W)}
    (hS : MeasurableSet S) :
    ∫ y, S.indicator (fun _ => (1 : ℝ)) y.1.1
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) =
      (growthPathLaw W b S).toReal := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have e1 := integral_fun_fst (μ := sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M) (ν := phaseLaw)
    (fun x : SampledPath W p M => S.indicator (fun _ => (1 : ℝ)) x.1)
  have e2 := integral_fun_fst (μ := growthPathLaw W b)
    (ν := (Measure.pi fun i : Fin p × Fin M => tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q i.1)).prod
      (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W)))
    (fun x : GrowthPath W => S.indicator (fun _ => (1 : ℝ)) x)
  have hpr : IsProbabilityMeasure ((Measure.pi fun i : Fin p × Fin M =>
      tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q i.1)).prod
      (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) := by
    have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q x.1)) :=
      fun x => Sampling.isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
    infer_instance
  simp only [probReal_univ, one_smul] at e1 e2
  rw [e1]
  unfold sampledPathLaw
  rw [e2]
  have e3 := integral_indicator_one (μ := growthPathLaw W b) hS
  rw [Pi.one_def] at e3
  rw [e3, measureReal_def]

/-- **`0 ≤ capped ≤ P_W(physCapEvent)`.** -/
theorem capped_mem (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x)
    (ha : ∀ j i, 0 ≤ a j i) :
    0 ≤ cappedClosedTransform b E s T h q a K M W ∧
      cappedClosedTransform b E s T h q a K M W ≤
        (growthPathLaw W b (physCapEvent b E s h K W)).toReal := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  set ν := (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw
  set S := physCapEvent b E s h K W
  set SM := physCapEventM b E s h K W
  have hSM := measurableSet_physCapEventM b E s h K W
  have hgi := integrable_cappedIntegrand (W := W) (M := M) (s := s) (h := h) (K := K) (T := T)
    (a := a) hb hE1 hE2 hq ha
  have hpt : ∀ y : SampledPath W p M × ℝ,
      0 ≤ S.indicator (fun _ => (1 : ℝ)) y.1.1 * closedIntegrand b E s T h q a M W y ∧
      S.indicator (fun _ => (1 : ℝ)) y.1.1 * closedIntegrand b E s T h q a M W y ≤
        S.indicator (fun _ => (1 : ℝ)) y.1.1 := by
    intro y
    have hf := closedIntegrand_mem b E s T h hq ha M W y
    by_cases hy : y.1.1 ∈ S
    · rw [Set.indicator_of_mem hy, one_mul]; exact hf
    · rw [Set.indicator_of_notMem hy, zero_mul]; exact ⟨le_rfl, le_rfl⟩
  have hci : Integrable (fun y : SampledPath W p M × ℝ => SM.indicator (fun _ => (1 : ℝ)) y.1.1)
      ν := by
    refine Integrable.of_bound (((measurable_const.indicator hSM).comp
      measurable_fst.fst).aestronglyMeasurable) 1 (ae_of_all _ fun y => ?_)
    by_cases hy : y.1.1 ∈ SM
    · rw [Set.indicator_of_mem hy]; norm_num
    · rw [Set.indicator_of_notMem hy]; norm_num
  have hae := ae_indicator_eq (s := s) (h := h) (K := K) (T := T) (M := M) (W := W) hb hE1 hE2 hq
  refine ⟨integral_nonneg fun y => (hpt y).1, ?_⟩
  rw [cappedClosedTransform, measure_congr (physCapEvent_ae_eq (W := W) hb hE1 hE2 s h K),
    ← integral_pathIndicator (T := T) (M := M) hq hSM]
  refine integral_mono_ae hgi hci ?_
  filter_upwards [hae] with y hy
  rw [← hy]
  exact (hpt y).2

end BlockBand.SourceProcess.CapCond
