module

public import BlockBand.SourceProcess.ClosedReduce.Defs
public import BlockBand.SourceProcess.ModelExist.Result
public import BlockBand.SourceProcess.SourceProcessLaw.Entrance
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction
public import BlockBand.SourceProcess.SourcePins.AtomLimit
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# `ClosedLimitLaw` from `CapCondLimit` and `TestedOfFinite`

* `closedLimitLaw_of_identification`: `ClosedLimitIdentification` and `TestedOfFinite`
  give `ClosedLimitLaw`. The tested model of the same entrance has the same capped value
  (`setIntegral_capSet_eq` with the proved `ModelUnique`). With
  `closedLimitIdentification_of_law`, `ClosedLimitLaw` thus differs from
  `ClosedLimitIdentification` only by the model-level `TestedOfFinite`.
* `closedLimitIdentification_of_capCond`, `closedLimitLaw_of_capCond`: the same from
  `CapCondLimit` and `TransmissionLawContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal

/-- **`ClosedLimitLaw` from `ClosedLimitIdentification` and `TestedOfFinite`.** -/
theorem closedLimitLaw_of_identification (hI : ClosedLimitIdentification)
    (hT : TestedOfFinite) : ClosedLimitLaw := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hI b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM).and_eventually
    hpos).mono fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω₁, m₁, 𝓖₁, Q₁, tseq₁, τ₁, G₁, hM₁, hval⟩ := hKL φ hφ L hφL
  obtain ⟨Ω₂, m₂, Q₂, tseq₂, τ₂, G₂, hT₂⟩ :=
    hT b hb0 hb E hE1 hE2 s T hs hsT p q hq _ h K M hh hM Ω₁ m₁ 𝓖₁ Q₁ tseq₁ τ₁ G₁ hM₁
  refine ⟨Ω₂, m₂, Q₂, tseq₂, τ₂, G₂, hT₂, ?_⟩
  have hM₂ := hT₂.isFiniteSourceModel (by linarith) hq
  rw [setIntegral_capSet_eq (a := a) modelUnique_holds hb0 hb hE1 hE2 hs hsT hq hh hM le_rfl hM₂
    hM₁ (T - s).toNNReal]
  exact hval

/-- **`ClosedLimitIdentification` from `CapCondLimit` and `TransmissionLawContract`**
(`ModelExists` and `ModelUnique` are proved, not hypotheses).
-/
theorem closedLimitIdentification_of_capCond (hTL : TransmissionLawContract)
    (hC : CapCondLimit) : ClosedLimitIdentification := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hC b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM).and_eventually
    hpos).mono fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨hz, hnz⟩ := hKL φ hφ L hφL
  obtain ⟨ρ, hρ, hρs, hρe⟩ :=
    entrance_sequence (SourcePins.entranceAtomic_of hTL) seqExtraction_holds hb0 hb hE1 hE2 hlim hs
  obtain ⟨Ω₂, m₂, 𝓖₂, Q₂, tseq₂, τ₂, G₂, hM₂⟩ :=
    ModelExist.modelExists_holds b hb0 hb E hE1 hE2 s T hs hsT p q hq ρ hρ hρs h K M hh hM
  rw [hρe] at hM₂
  refine ⟨Ω₂, m₂, 𝓖₂, Q₂, tseq₂, τ₂, G₂, hM₂, ?_⟩
  have hS := measurableSet_capSet K h
  have hQA := measure_entEvent hM₂ hS
  by_cases h0 : entranceLaw P μ s (capSet K h) = 0
  · rw [setIntegral_measure_zero _ (hQA.trans h0), hz h0]
  obtain ⟨Ω₁, m₁, 𝓖₁, Q₁, tseq₁, τ₁, G₁, hM₁, hval⟩ := hnz h0
  have hM₃ := condModel hM₂ hS h0
  have hlaw := modelUnique_holds b hb0 hb E hE1 hE2 s T hs hsT p q hq _ h K M hh hM Ω₁ _ 𝓖₁ _ _ _ _
    hM₁ Ω₂ _ 𝓖₂ _ _ _ _ hM₃ (T - s).toNNReal
  have hf := measurable_sampledTransformValue (K := K) (M := M) a
  have e1 : ∫ ω, sampledTransformValue a (G₁ (T - s).toNNReal ω) ∂Q₁ =
      ∫ ω, sampledTransformValue a (G₂ (T - s).toNNReal ω) ∂(Q₂[|entEvent tseq₂ (capSet K h)]) := by
    rw [← integral_map (model_measurable_G hM₁ _).aemeasurable hf.aestronglyMeasurable, hlaw,
      integral_map (model_measurable_G hM₃ _).aemeasurable hf.aestronglyMeasurable]
  have hfin : entranceLaw P μ s (capSet K h) ≠ ∞ := by
    rw [← hQA]
    have := hM₂.prob
    exact measure_ne_top _ _
  rw [← hval, e1]
  simp only [ProbabilityTheory.cond, integral_smul_measure, hQA, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 hfin, ENNReal.toReal_one,
    one_mul]

/-- **`ClosedLimitLaw` from `CapCondLimit`, `TestedOfFinite` and `TransmissionLawContract`.**
-/
theorem closedLimitLaw_of_capCond (hTL : TransmissionLawContract) (hC : CapCondLimit)
    (hT : TestedOfFinite) : ClosedLimitLaw :=
  closedLimitLaw_of_identification (closedLimitIdentification_of_capCond hTL hC) hT

/-- **The same from the four input hypotheses.** -/
theorem closedLimitLaw_of_capCond_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hC : CapCondLimit) (hT : TestedOfFinite) : ClosedLimitLaw :=
  closedLimitLaw_of_capCond (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hC hT

end BlockBand.SourceProcess.ClosedReduce
