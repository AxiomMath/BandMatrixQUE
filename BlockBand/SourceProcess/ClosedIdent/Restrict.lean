module

public import BlockBand.SourceProcess.ClosedIdent.Defs
public import BlockBand.Transmission.LawDuality.TightAbsorbed

/-!
# Removing the restriction to the cap events costs at most their complements

* `closed_sub_capped_mem`: `0 ≤ closed − capped ≤ P_W(physCapEventᶜ)`.
* `model_sub_restrict_mem`: `0 ≤ v − ∫_{t_K ≤ h²} F ≤ entrance (capSet K h)ᶜ` in every model.
* `physCapEvent_ae_eq`: the physical cap event agrees a.s. with the Borel set `physCapEventM`
  (the trace measure replaced by the measurable `clampedTraceMeasure`, equal on `0 ⪯ T ⪯ I`).
  So the integrand of `cappedClosedTransform` is a.e. strongly measurable
  (`integrable_cappedIntegrand`): the statement is not degenerate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedIdent

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.LawDuality BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ENNReal

variable {W : ℕ}

/-- The Borel version of the physical cap event. -/
def physCapEventM (b E s h : ℝ) (K W : ℕ) : Set (GrowthPath W) :=
  {ω | ((clampedTraceMeasure (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω) :
    FiniteMeasure unitInterval) : Measure unitInterval) ∈ capSet K h}

theorem measurableSet_physCapEventM (b E s h : ℝ) (K W : ℕ) :
    MeasurableSet (physCapEventM b E s h K W) :=
  (measurable_subtype_coe.comp (measurable_clampedTraceMeasure.comp
    (measurable_pathTransmission b E _ _))) (measurableSet_capSet K h)

theorem physCapEvent_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    (K : ℕ) : physCapEvent b E s h K W =ᵐ[growthPathLaw W b] physCapEventM b E s h K W := by
  filter_upwards [Transmission.Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb
    hE1 hE2] with ω hω
  have e : transmissionProcess b E (fun _ => 0) W s ω =
      clampedTraceMeasure (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω) := by
    rw [clampedTraceMeasure, ite_eq_left ⟨Transmission.Bridge.pathTransmission_posSemidef hω _,
      Transmission.Bridge.one_sub_pathTransmission_posSemidef b E _ W _ ω⟩]
    rfl
  change (((transmissionProcess b E (fun _ => 0) W s ω : FiniteMeasure unitInterval) :
    Measure unitInterval) ∈ capSet K h) = _
  rw [e]
  rfl

section Phys

variable {b E s T h : ℝ} {p J : ℕ} {q : Fin p → ℝ → ℝ} {a : Fin J → Fin p → ℝ} {K M : ℕ}

theorem isProbabilityMeasure_sampledPathLaw (hq : ∀ i x, 0 ≤ q i x) (n : ℕ) :
    IsProbabilityMeasure (sampledPathLaw b W n q M) := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => Sampling.isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
  unfold sampledPathLaw; infer_instance

/-- The cap indicator, read on the path coordinate, is a.e. the Borel one. -/
theorem ae_indicator_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x) :
    ∀ᵐ y ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw),
      (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 =
        (physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have h1 : Measure.QuasiMeasurePreserving Prod.fst (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M)
      (growthPathLaw W b) := Measure.quasiMeasurePreserving_fst
  have h2 := h1.comp (Measure.quasiMeasurePreserving_fst (μ := sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M)
    (ν := phaseLaw))
  exact h2.ae (indicator_ae_eq_of_ae_eq_set (physCapEvent_ae_eq hb hE1 hE2 s h K))

theorem integrable_cappedIntegrand (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hq : ∀ i x, 0 ≤ q i x) (ha : ∀ j i, 0 ≤ a j i) :
    Integrable (fun y : SampledPath W p M × ℝ =>
      (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
        closedIntegrand b E s T h q a M W y)
      ((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have hm : Measurable fun y : SampledPath W p M × ℝ =>
      (physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
        closedIntegrand b E s T h q a M W y :=
    ((measurable_const.indicator (measurableSet_physCapEventM b E s h K W)).comp
      measurable_fst.fst).mul (measurable_closedIntegrand b E s T h q a M W)
  refine Integrable.of_bound (hm.aestronglyMeasurable.congr ?_) 1 (ae_of_all _ fun y => ?_)
  · filter_upwards [ae_indicator_eq (s := s) (h := h) (K := K) (T := T) hb hE1 hE2 hq] with y hy
    rw [hy]
  · have hf := closedIntegrand_mem b E s T h hq ha M W y
    rw [Real.norm_eq_abs, abs_le]
    by_cases hy : y.1.1 ∈ physCapEvent b E s h K W
    · rw [Set.indicator_of_mem hy, one_mul]; constructor <;> linarith [hf.1, hf.2]
    · rw [Set.indicator_of_notMem hy, zero_mul]; constructor <;> norm_num

/-- **`0 ≤ closed − capped ≤ P_W(more than K retained modes)`.** -/
theorem closed_sub_capped_mem (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hq : ∀ i x, 0 ≤ q i x) (ha : ∀ j i, 0 ≤ a j i) :
    0 ≤ closedSampledTransform b E s T h q a M W - cappedClosedTransform b E s T h q a K M W ∧
      closedSampledTransform b E s T h q a M W - cappedClosedTransform b E s T h q a K M W ≤
        (growthPathLaw W b (physCapEvent b E s h K W)ᶜ).toReal := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  set ν := (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw
  set S := physCapEvent b E s h K W
  set f := closedIntegrand b E s T h q a M W
  have hfi : Integrable f ν := integrable_closedIntegrand b E s T h hq ha M W
  have hgi := integrable_cappedIntegrand (W := W) (M := M) (s := s) (h := h) (K := K) (T := T)
    hb hE1 hE2 hq ha
  have hdiff : closedSampledTransform b E s T h q a M W - cappedClosedTransform b E s T h q a K M W
      = ∫ y, (f y - S.indicator (fun _ => (1 : ℝ)) y.1.1 * f y) ∂ν := by
    rw [closedSampledTransform_eq, cappedClosedTransform, integral_sub hfi hgi]
  have hpt : ∀ y : SampledPath W p M × ℝ, 0 ≤ f y - S.indicator (fun _ => (1 : ℝ)) y.1.1 * f y ∧
      f y - S.indicator (fun _ => (1 : ℝ)) y.1.1 * f y ≤ Sᶜ.indicator (fun _ => (1 : ℝ)) y.1.1 := by
    intro y
    have hf := closedIntegrand_mem b E s T h hq ha M W y
    by_cases hy : y.1.1 ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hy)]
      constructor <;> linarith
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_mem (Set.mem_compl hy)]
      constructor <;> linarith [hf.1, hf.2]
  set SM := physCapEventM b E s h K W
  have hSM := measurableSet_physCapEventM b E s h K W
  have hcae : ∀ᵐ y ∂ν, Sᶜ.indicator (fun _ => (1 : ℝ)) y.1.1 =
      SMᶜ.indicator (fun _ => (1 : ℝ)) y.1.1 := by
    filter_upwards [ae_indicator_eq (s := s) (h := h) (K := K) (T := T) hb hE1 hE2 hq] with y hy
    rw [Set.indicator_compl, Set.indicator_compl, Pi.sub_apply, Pi.sub_apply]
    exact congrArg _ hy
  have hci : Integrable (fun y : SampledPath W p M × ℝ => SMᶜ.indicator (fun _ => (1 : ℝ)) y.1.1)
      ν := by
    refine Integrable.of_bound (((measurable_const.indicator hSM.compl).comp
      measurable_fst.fst).aestronglyMeasurable) 1 (ae_of_all _ fun y => ?_)
    by_cases hy : y.1.1 ∈ SMᶜ
    · rw [Set.indicator_of_mem hy]; norm_num
    · rw [Set.indicator_of_notMem hy]; norm_num
  have hval : ∫ y, SMᶜ.indicator (fun _ => (1 : ℝ)) y.1.1 ∂ν =
      (growthPathLaw W b Sᶜ).toReal := by
    have e1 := integral_fun_fst (μ := sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M) (ν := phaseLaw)
      (fun x : SampledPath W p M => SMᶜ.indicator (fun _ => (1 : ℝ)) x.1)
    have e2 := integral_fun_fst (μ := growthPathLaw W b)
      (ν := (Measure.pi fun i : Fin p × Fin M => tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q i.1)).prod
        (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W)))
      (fun x : GrowthPath W => SMᶜ.indicator (fun _ => (1 : ℝ)) x)
    have hpr : IsProbabilityMeasure ((Measure.pi fun i : Fin p × Fin M =>
        tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q i.1)).prod
        (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) := by
      have : ∀ x : Fin p × Fin M, IsProbabilityMeasure
          (tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q x.1)) :=
        fun x => Sampling.isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
      infer_instance
    simp only [probReal_univ, one_smul] at e1 e2
    rw [e1]
    unfold sampledPathLaw
    rw [e2]
    have e3 := integral_indicator_one (μ := growthPathLaw W b) hSM.compl
    rw [Pi.one_def] at e3
    rw [e3, measureReal_def, measure_congr (physCapEvent_ae_eq hb hE1 hE2 s h K).compl]
  rw [hdiff]
  refine ⟨integral_nonneg fun y => (hpt y).1, ?_⟩
  rw [← hval, ← integral_congr_ae hcae]
  exact integral_mono (hfi.sub hgi) (hci.congr (hcae.mono fun y hy => hy.symm))
    fun y => (hpt y).2

end Phys

/-- **Model side**: `0 ≤ v − ∫_{t_K ≤ h²} F ≤ entrance (capSet K h)ᶜ` for the model transform. -/
theorem model_sub_restrict_mem {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K M J : ℕ}
    {a : Fin J → Fin p → ℝ} {entrance : Measure (Measure unitInterval)} {Ω : Type}
    [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) (ha : ∀ j i, 0 ≤ a j i)
    (t : ℝ≥0) :
    0 ≤ ∫ ω, sampledTransformValue a (G t ω) ∂Q -
        ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G t ω) ∂Q ∧
      ∫ ω, sampledTransformValue a (G t ω) ∂Q -
        ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G t ω) ∂Q ≤
        (entrance (capSet K h)ᶜ).toReal := by
  have hS := measurableSet_capSet K h
  have hA := 𝓖.le 0 _ (measurableSet_entEvent hM hS)
  have hsplit := integral_add_compl hA (integrable_transform hM ha t)
  have hc : Q (entEvent tseq (capSet K h))ᶜ = entrance (capSet K h)ᶜ :=
    measure_entEvent hM hS.compl
  have b1 := setIntegral_transform_mem hM ha t (entEvent tseq (capSet K h))ᶜ
  rw [hc] at b1
  rw [← hsplit]
  constructor <;> linarith [b1.1, b1.2]

end BlockBand.SourceProcess.ClosedIdent
