module

public import BlockBand.SourceProcess.HorizonExt.Holds
public import BlockBand.SourceProcess.BornRestart.Holds
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorOn
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorNoLoss
public import BlockBand.SourceProcess.ComplexUnique.Bounds

/-!
# No rank creation and no rank loss on a birth-free segment of a born Gram solution

`rank_segment` (proved in the sibling module `RankSeg`): let `G` be a born
Gram solution with deterministic births `β₀` and no birth in
`(a, a + h)`. Then a.s., for every `k`: if `e_k(B(a)) = 0` then `e_k(B(a + u)) = 0` for all
`u < h`, and if `e_k(B(a)) > 0` then `e_k(B(a + u)) > 0` for all `u < h`; the same for `M - B`.

Proof: restart at `a` (`bornRestart_holds`), the birth-free part up to `r < h` is a horizon
solution (`isGramHorizonSolution_tilde`), glue it to an ambient solution
(`exists_global_extension`, the construction of `gramHorizonExtension_holds` kept pathwise), and
apply the rank corollaries (`RankCorOn`, `RankCorNoLoss`) to the global solution; its
path is the original one on `[0, r]`, for every point of the product space. This file proves
`exists_global_extension` and the rank statement for the global solution, `rank_global`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornStopped
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.HorizonExt
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.BornRestart
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type} [Fintype c] [DecidableEq c]

/-- **A horizon solution extends to a global one with the same path on `[0, r]`** (the
construction of `gramHorizonExtension_holds`, kept pathwise). -/
theorem exists_global_extension {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {r : ℝ≥0} {Ω : Type} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {G : ℝ≥0 → Ω → GramState c}
    (hG : IsGramHorizonSolution Q 𝓖 D0 D r G) :
    ∃ (W : Type) (_ : MeasurableSpace W) (ν : Measure W) (_ : IsProbabilityMeasure ν)
      (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W)))
      (Ĝ : ℝ≥0 → Ω × W → GramState c),
      IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Ĝ ∧ ∀ t ≤ r, ∀ x, Ĝ t x = G t x.1 := by
  have hq := (measurePreserving_fst (μ := Q)
    (ν := commonWienerLaw (SourceNoise (c ⊕ c)))).quasiMeasurePreserving
  have hcomap := comap_fst_le_driverAugmented (κ := SourceNoise (c ⊕ c)) Q
  have hGr := SourceProcessLaw.measurable_of_stronglyMeasurable_gram (𝓖.le r) (hG.adapted r)
  set ξ : DriverSample Ω (SourceNoise (c ⊕ c)) → Matrix (c ⊕ c) c ℂ :=
    fun x => sqrtFrame (G r x.1) with hξ
  have hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise (c ⊕ c)) Q 0] ξ := by
    have : BorelSpace (Matrix (c ⊕ c) c ℂ) := inferInstanceAs (BorelSpace ((c ⊕ c) → c → ℂ))
    have : SecondCountableTopology (Matrix (c ⊕ c) c ℂ) :=
      inferInstanceAs (SecondCountableTopology ((c ⊕ c) → c → ℂ))
    have : TopologicalSpace.PseudoMetrizableSpace (Matrix (c ⊕ c) c ℂ) :=
      inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace ((c ⊕ c) → c → ℂ))
    exact (((measurable_sqrtFrame.comp hGr).comp (comap_measurable Prod.fst)).mono hcomap
      le_rfl).stronglyMeasurable
  have hfr : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, GramFeasible D (G r x.1) := by
    filter_upwards [hq.ae hG.feasible] with x hx
    exact hx r le_rfl
  have hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, TwoProjection P0 D (ξ x) := by
    filter_upwards [hfr] with x hx
    exact twoProjection_sqrtFrame hD hx
  obtain ⟨X, hX⟩ := (SourceSDE.finiteSourceWellPosed_holds Q D0 (Fintype.card c) P0 D hD0
    isNearProjection_P0 hD ξ hξm hξc).1
  have hY := GramUniqueness.ambient_isGramMartingaleSolution Q hD0 isNearProjection_P0 hD hξm
    hξc hX
  have h0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, gramPair P0 (X 0 x) = G r x.1 := by
    filter_upwards [hX.2, hfr] with x h1 h2
    rw [h1, hξ, gramPair_sqrtFrame h2]
  exact ⟨_, inferInstance, commonWienerLaw (SourceNoise (c ⊕ c)), inferInstance,
    glueFil 𝓖 (driverAugmented (κ := SourceNoise (c ⊕ c)) Q) hcomap r,
    glueProc r G fun t x => gramPair P0 (X t x), isGramMartingaleSolution_glue hcomap hG hY h0,
    fun t ht x => by rw [glueProc_of_le ht]⟩

theorem ae_of_ae_prod_fst {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W] {Q : Measure Ω}
    {ν : Measure W} [IsProbabilityMeasure ν] {P : Ω → Prop}
    (h : ∀ᵐ x ∂(Q.prod ν), P x.1) : ∀ᵐ ω ∂Q, P ω := by
  rw [ae_iff] at h ⊢
  have e : {x : Ω × W | ¬P x.1} = {ω | ¬P ω} ×ˢ univ := by ext x; simp
  rw [e, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

/-- On a global Gram solution: a.s. no rank creation and no rank loss at any time. -/
theorem rank_global {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {G : ℝ≥0 → Ω → GramState c}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) :
    ∀ᵐ ω ∂Q, (principalMinorSum k (G 0 ω).2 = 0 → ∀ t, principalMinorSum k (G t ω).2 = 0) ∧
      (0 < principalMinorSum k (G 0 ω).2 → ∀ t, 0 < principalMinorSum k (G t ω).2) ∧
      (principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0 →
        ∀ t, principalMinorSum k ((G t ω).1 - (G t ω).2) = 0) ∧
      (0 < principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) →
        ∀ t, 0 < principalMinorSum k ((G t ω).1 - (G t ω).2)) := by
  have hm0 : StronglyMeasurable[𝓖 0] (G 0) := hG.adapted 0
  have hf1 : Continuous fun H : GramState c => principalMinorSum k H.2 :=
    (contDiff_ek_snd k).continuous
  have hf2 : Continuous fun H : GramState c => principalMinorSum k (H.1 - H.2) :=
    (contDiff_ek_fst_sub_snd k).continuous
  have hA1 : MeasurableSet[𝓖 0] {ω | principalMinorSum k (G 0 ω).2 = 0} :=
    measurableSet_eq_fun (hf1.comp_stronglyMeasurable hm0).measurable measurable_const
  have hA2 : MeasurableSet[𝓖 0] {ω | principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0} :=
    measurableSet_eq_fun (hf2.comp_stronglyMeasurable hm0).measurable measurable_const
  filter_upwards [principalMinorSum_near_ae_forall_eq_zero_on hD0 hD hG k hA1
      (Eventually.of_forall fun _ h => h),
    principalMinorSum_far_ae_forall_eq_zero_on hD0 hD hG k hA2 (Eventually.of_forall fun _ h => h),
    principalMinorSum_near_ae_forall_pos hD0 hD hG k, principalMinorSum_far_ae_forall_pos hD0 hD hG k,
    hG.continuous] with ω h1 h2 h3 h4 hc
  have hK : ∀ t : ℝ≥0, ∃ K : ℕ, (t : WithTop ℝ≥0) ≤ gramTraceStop G K ω := exists_lt_gramTraceStop hc
  refine ⟨fun h t => ?_, fun h t => ?_, fun h t => ?_, fun h t => ?_⟩ <;>
    obtain ⟨K, hK⟩ := hK t
  · have := h1 h t K; rwa [stoppedProcess_eq_stopTime, stopTime_eq_self hK] at this
  · have := h3 h t K; rwa [stoppedProcess_eq_stopTime, stopTime_eq_self hK] at this
  · have := h2 h t K; rwa [stoppedProcess_eq_stopTime, stopTime_eq_self hK] at this
  · have := h4 h t K; rwa [stoppedProcess_eq_stopTime, stopTime_eq_self hK] at this

end BlockBand.SourceProcess.ComplexUnique
