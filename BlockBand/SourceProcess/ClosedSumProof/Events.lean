module

public import BlockBand.SourceProcess.ClosedSumProof.Adapted
public import BlockBand.SourceProcess.ClosedSumProof.Pins
public import BlockBand.SourceProcess.ClosedIdent.Restrict
public import BlockBand.SourceProcess.Sampling.Mix
public import BlockBand.Transmission.LawForced.Discrete

/-!
# Measurable versions of the alive events

`physCapEvent` is defined through `transmissionProcess` and is not known to be measurable;
`physCapEventM` is Borel and a.e. equal (`physCapEvent_ae_eq`). `aliveM` is `closedAlive`
with `physCapEventM`:
* `measurableSet_aliveM`, `measurableSet_noBirth`: both are `closedSigma W j`-events (for an
  admissible frame and `j ≥ n_s`);
* `closedAlive_ae_eq`: `closedAlive =ᵐ aliveM` under `sampledPathLaw ⊗ phaseLaw`;
* `lintegral_condErr_congr`, `lintegral_indicator_congr`: the integrands of `ClosedSummed` and
  `ClosedFourth` may be computed with `aliveM`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.LawDuality BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.Bridge

variable {W p K M : ℕ}

/-- `closedAlive` with the Borel cap event. -/
def aliveM (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (SampledPath W p M × ℝ) :=
  {y | y.1.1 ∈ physCapEventM b E s h K W ∧ ∀ i, closeLen s W ≤ i → i ≤ j →
    ((closedGramAt b E s T h q W i Vs y).1.trace).re < R}

theorem measurableSet_capM (b E s h : ℝ) (K W : ℕ) :
    MeasurableSet[growthSigma W (closeLen s W)] (physCapEventM b E s h K W) :=
  (measurable_subtype_coe.comp (measurable_clampedTraceMeasure.comp
    (BlockBand.Transmission.LawForced.measurable_pathTransmission_adapted b E _ _))) (measurableSet_capSet K h)

theorem measurable_traceRe_past (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) {i j : ℕ}
    (hi : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[closedSigma W j p M] fun y =>
      ((closedGramAt b E s T h q W i Vs y).1.trace).re := by
  have hG := (measurable_closedGramAt_past (M := M) b E s T h q hi hVs).mono
    (closedSigma_mono hij) le_rfl
  exact Complex.measurable_re.comp ((measurable_trace (M := id) measurable_id).comp
    (measurable_fst.comp hG))

/-- The path coordinate is measurable from `closedSigma W j` to `growthSigma W i`, `i ≤ j`. -/
theorem measurable_path_closed {i j : ℕ} (hij : i ≤ j) :
    Measurable[closedSigma W j p M, growthSigma W i] fun y : SampledPath W p M × ℝ => y.1.1 := by
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact ((measurable_restrictPast hij).comp (measurable_fst.comp (measurable_closedGen j))) hT

theorem measurableSet_aliveM (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) :
    MeasurableSet[closedSigma W j p M] (aliveM b E s T h q R W j Vs) := by
  have e : aliveM (M := M) b E s T h q R W j Vs =
      (fun y : SampledPath W p M × ℝ => y.1.1) ⁻¹' physCapEventM b E s h K W ∩
        ⋂ i ∈ Finset.Icc (closeLen s W) j,
          {y | ((closedGramAt b E s T h q W i Vs y).1.trace).re < R} := by
    ext y
    simp only [aliveM, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter,
      Finset.mem_Icc]
    exact and_congr Iff.rfl ⟨fun h i hi => h i hi.1 hi.2, fun h i h1 h2 => h i ⟨h1, h2⟩⟩
  rw [e]
  refine MeasurableSet.inter ?_ (Finset.measurableSet_biInter _ fun i hi => ?_)
  · exact measurable_path_closed hj (measurableSet_capM b E s h K W)
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    exact measurableSet_lt (measurable_traceRe_past b E s T h q h1 h2 hVs) measurable_const

theorem measurableSet_noBirth (j : ℕ) :
    MeasurableSet[closedSigma W j p M] (noBirth (W := W) (p := p) (M := M) j) := by
  have e : noBirth (W := W) (p := p) (M := M) j =
      ⋂ il : Fin p × Fin M, {y | y.1.2.1 il ≠ j} := by
    ext y; simp [noBirth]
  rw [e]
  refine MeasurableSet.iInter fun il => ?_
  have hf : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ => y.1.2.1 il :=
    ((measurable_pi_apply il).comp (measurable_fst.comp (measurable_fst.comp measurable_snd))).comp
      (measurable_closedGen j)
  exact hf (measurableSet_singleton j).compl

/-- The path coordinate is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_path {b : ℝ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (n : ℕ) :
    Measure.QuasiMeasurePreserving (fun y : SampledPath W p M × ℝ => y.1.1)
      ((sampledPathLaw b W n q M).prod phaseLaw) (growthPathLaw W b) := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => Sampling.isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
  exact (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
    (Measure.quasiMeasurePreserving_fst (μ := sampledPathLaw b W n q M) (ν := phaseLaw))

theorem capPre_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (n : ℕ) :
    {y : SampledPath W p M × ℝ | y.1.1 ∈ physCapEvent b E s h K W} =ᵐ[(sampledPathLaw b W n q M).prod
      phaseLaw] {y | y.1.1 ∈ physCapEventM b E s h K W} :=
  (quasiMeasurePreserving_path hq n).preimage_ae_eq (physCapEvent_ae_eq hb hE1 hE2 s h K)

theorem closedAlive_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s T h : ℝ)
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (n : ℕ) (R : ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    closedAlive (M := M) b E s T h q R W j Vs =ᵐ[(sampledPathLaw b W n q M).prod phaseLaw]
      aliveM b E s T h q R W j Vs := by
  have e1 : closedAlive (M := M) b E s T h q R W j Vs =
      {y | y.1.1 ∈ physCapEvent b E s h K W} ∩ {y | ∀ i, closeLen s W ≤ i → i ≤ j →
        ((closedGramAt b E s T h q W i Vs y).1.trace).re < R} := rfl
  have e2 : aliveM (M := M) b E s T h q R W j Vs =
      {y | y.1.1 ∈ physCapEventM b E s h K W} ∩ {y | ∀ i, closeLen s W ≤ i → i ≤ j →
        ((closedGramAt b E s T h q W i Vs y).1.trace).re < R} := rfl
  rw [e1, e2]
  exact (capPre_ae_eq hb hE1 hE2 s h hq n).inter (Filter.EventuallyEq.refl _ _)

variable {Ω : Type*} {F : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {μ : Measure Ω}

/-- The conditional error integrands agree for a.e.-equal events. -/
theorem lintegral_condErr_congr {A A' : Set Ω} (hA : A =ᵐ[μ] A')
    (f g : Ω → ℂ) :
    ∫⁻ y, ‖A.indicator (fun y => μ[A.indicator f | F] y - g y) y‖ₑ ∂μ =
      ∫⁻ y, ‖A'.indicator (fun y => μ[A'.indicator f | F] y - g y) y‖ₑ ∂μ := by
  have h1 : μ[A.indicator f | F] =ᵐ[μ] μ[A'.indicator f | F] :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hA)
  refine lintegral_congr_ae ?_
  filter_upwards [h1, hA] with y hy hyA
  have hyA' : (y ∈ A) ↔ (y ∈ A') := Iff.of_eq hyA
  by_cases h : y ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hyA'.mp h), hy]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hyA'.mpr h'))]

/-- Indicator integrands agree for a.e.-equal events. -/
theorem lintegral_indicator_congr {A A' : Set Ω} (hA : A =ᵐ[μ] A') (f : Ω → ℂ) (k : ℕ) :
    ∫⁻ y, ‖A.indicator f y‖ₑ ^ k ∂μ = ∫⁻ y, ‖A'.indicator f y‖ₑ ^ k ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := f) hA] with y hy
  rw [hy]

end BlockBand.SourceProcess.ClosedSumProof
