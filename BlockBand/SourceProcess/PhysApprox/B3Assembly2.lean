module

public import BlockBand.SourceProcess.PhysApprox.B3Pins2
public import BlockBand.SourceProcess.PhysApprox.B3Assembly
public import BlockBand.SourceProcess.PhysApprox.B3Bridge
public import BlockBand.SourceProcess.PhysApprox.B3Atom
public import BlockBand.SourceProcess.PhysApprox.B3GenSplit
public import BlockBand.SourceProcess.PhysApprox.IdentCap
public import BlockBand.SourceProcess.PhysApprox.IdentLimit
public import BlockBand.SourceProcess.PhysApprox.IdentTested
public import BlockBand.SourceProcess.PhysApprox.TagLeakHolds
public import BlockBand.SourceProcess.ComplexCoupled.Closes
public import BlockBand.SourceProcess.ClosedReduce.StartAE
public import BlockBand.SourceProcess.ClosedReduce.Edge

/-!
# The final assembly of the frequent-`h` physical approximation

This file removes the hypothesis `ComplexModelExists` from the composition through
`ComplexCapCondLimit`, shows that the closed limit identification implies `ComplexCapCondLimit`, and
proves `ComplexCapCondLimit` from the finite-`W` estimates.

* `freq_of_capCond_noEx`: the physical approximation from `ComplexCapCondLimit`, without
  `ComplexModelExists`.
* `capCond_of_identification`: `ComplexClosedLimitIdentification` implies `ComplexCapCondLimit`.
* `complexCapCondLimit_of_pins`, `complexPhysicalApproximationFreq_final`: `ComplexCapCondLimit` and
  the physical approximation from the finite-`W` hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal

/-!
## Removing `ComplexModelExists`; the closed Gram state at the start
-/

/-- T9 without T8 and without `ComplexModelExists`. -/
theorem freq_of_capCond_noEx (t1 : TargetT1) (t2 : TargetT2) (t3 : TargetT3) (t4 : TargetT4)
    (tL : TargetTL) (t6 : TargetT6) (t7 : TargetT7)
    (hMT : Layers.MatchedTracesContract) (hGA : Layers.GaussianAbsorptionContract)
    (hSR : Layers.ScalarRecursionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate) (hC : ComplexCapCondLimit) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_of_capCond t1 t2 t3 t4 tL t6 t7 hMT hGA hSR hLp hP hK
    ComplexCoupled.complexModelExists_holds' hC

/-- The converse of R1: (b2) gives `ComplexCapCondLimit`. -/
theorem capCond_of_identification (hI : ComplexClosedLimitIdentification) :
    ComplexCapCondLimit := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  refine (hI b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).mono fun h hK => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', mΩ', 𝓖, Q, tseq, G, Kc, hM, hval⟩ := hKL φ hφ L hφL
  have hS := measurableSet_capSet K h
  have hQA := ComplexCapLimit.cmeasure_entEvent hM hS
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [← hval]
    unfold restrictedModelExpectation
    exact setIntegral_measure_zero _ (hQA.trans h0)
  · refine ⟨Ω', mΩ', 𝓖, _, tseq, G, Kc, ComplexCapLimit.ccondModel hM hS h0, ?_⟩
    have hfin : entranceLaw P μ s (capSet K h) ≠ ∞ := by
      rw [← hQA]
      have := hM.prob
      exact measure_ne_top _ _
    rw [← hval]
    unfold restrictedModelExpectation modelExpectation
    simp only [ProbabilityTheory.cond, integral_smul_measure, hQA, smul_eq_mul]
    rw [← mul_assoc, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 hfin, ENNReal.toReal_one,
      one_mul]

/-- The closed Gram process starts at `initialGram` for every admissible
time-`s` frame, almost surely, for every probe sample and phase.
-/
theorem ae_b3ClosedGramAt_start_adm {b E s h : ℝ} {np K W : ℕ} {τ m : Fin np → ℝ}
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hτ : ∀ i, s < τ i)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (g : Fin np → Fin W → ℂ) (θ : ℝ),
      b3ClosedGramAt b E s h τ m W (closeLen s W) Vs ((ω, g), θ) =
        initialGram K (Fin np) (physTseq b E s W ω) h := by
  filter_upwards [hVs.2, FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW]
    with ω ⟨hG, hE⟩ hU g θ
  have hA := ClosedReduce.omitted_mul_timeSFrame (Vs ω) (hU _).1 hG hE
  have hX : b3OpenFrameAt b E s τ m W (closeLen s W) Vs (ω, g) =
      Matrix.of fun z col => Sum.elim (fun k => Vs ω z k) (fun _ => (0 : ℂ)) col := by
    ext z (k | i)
    · simp [b3OpenFrameAt, stepProd]
    · simp [b3OpenFrameAt, probeFrame_start hτ]
  have hAX : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      b3OpenFrameAt b E s τ m W (closeLen s W) Vs (ω, g) = 0 := by
    rw [hX]
    ext z (k | i)
    · have := congrFun (congrFun hA z) k
      simpa [mul_apply] using this
    · simp [mul_apply]
  rw [b3ClosedGramAt, b3ClosedFrameAt, ClosedReduce.closedFix _ hAX, hX]
  have hG1 := congrArg Prod.fst hG
  have hG2 := congrArg Prod.snd hG
  rw [← curGramOf_initialGram (Fin np)] at hG1 hG2
  refine Prod.ext ?_ ?_
  · ext (k | i) (k' | i')
    · have := congrFun (congrFun hG1 k) k'
      simpa [gramPair, sourceGram, curGramOf, mul_apply] using this
    all_goals simp [gramPair, sourceGram, initialGram, initialFrame, mul_apply]
  · ext (k | i) (k' | i')
    · have := congrFun (congrFun hG2 k) k'
      simpa [gramPair, nearGram, curGramOf, mul_apply] using this
    all_goals simp [gramPair, nearGram, initialGram, initialFrame, mul_apply]

/-!
## The final assembly
-/

/-- **`ComplexCapCondLimit` from `TargetCapCond'`**: the six generator estimates
`GenReqGramDrift`, `GenReqGramBracket`, `GenReqBirth`, `KDriftSummed`, `KBracketSummed`,
`KConjSummed` are hypotheses, and every other hypothesis of `TargetCapCond'` is discharged. -/
theorem complexCapCondLimit_of_pins (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (tCap : TargetCapCond') (hGD : GenReqGramDrift)
    (hGB : GenReqGramBracket) (hB : GenReqBirth) (hKD : KDriftSummed) (hKB : KBracketSummed)
    (hKC : KConjSummed) (hT : ComplexClosedTight) (hKm : ComplexKStoppedMomentMax)
    (hCur : ComplexClosedCurrent) (hLind : ComplexClosedLindeberg) : ComplexCapCondLimit :=
  tCap (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
    ClosedReduce.existsTimeSFrame_holds (complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC)
    hT hKm hCur hLind

/-- **The final assembly** (stopped route): `ComplexPhysicalApproximationFreq` from the input
hypotheses, `KolmogorovConjugate`, `TargetT1`–`TargetT4`, `TargetCapCond'` and the finite-`W`
estimates. For (b): `complexCapCondLimit_of_pins` ⇒ R1 ⇒ (b2) ⇒ R3
(`ComplexClosedLimitLawStopped`) ⇒ `targetT8Stopped_holds` ⇒ (b2) ⇒ `targetT7_holds` ⇒
`targetT6_holds`. For (a): `targetTL_holds`, `TargetT4`, `TargetT3`, `TargetT2`, `TargetT1`. Then
`complexPhysicalApproximationFreq_of_pins`.
-/
theorem complexPhysicalApproximationFreq_final (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (t1 : TargetT1) (t2 : TargetT2) (t3 : TargetT3) (t4 : TargetT4)
    (tCap : TargetCapCond') (hGD : GenReqGramDrift) (hGB : GenReqGramBracket)
    (hB : GenReqBirth) (hKD : KDriftSummed) (hKB : KBracketSummed) (hKC : KConjSummed)
    (hT : ComplexClosedTight) (hKm : ComplexKStoppedMomentMax) (hCur : ComplexClosedCurrent)
    (hLind : ComplexClosedLindeberg) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hC := complexCapCondLimit_of_pins hMT hGA hLp hP tCap hGD hGB hB hKD hKB hKC hT hKm hCur
    hLind
  have hStop : ComplexClosedLimitLawStopped :=
    complexClosedLimitLawStopped_of_capCond_baseContracts hMT hGA hLp hP
      ComplexCoupled.complexModelExists_holds' hC
  have hb2 : ComplexClosedLimitIdentification := targetT8Stopped_holds hStop
  have hL := targetTL_holds hMT hGA hSR hLp hP
  exact complexPhysicalApproximationFreq_of_pins
    (t1 hMT hGA hSR hLp hP (t2 hMT hGA hSR hLp hP hK hL) (t3 hMT hGA hSR hLp hP hL (t4 hL)))
    (targetT6_holds hMT hGA hSR hLp hP (targetT7_holds hb2))

end BlockBand.SourceProcess.PhysApprox.B3
