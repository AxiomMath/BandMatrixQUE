module

public import BlockBand.SourceProcess.PhysApprox.B3Assembly2
public import BlockBand.SourceProcess.PhysApprox.B3LimPass
public import BlockBand.SourceProcess.PhysApprox.B3FeasBridge
public import BlockBand.SourceProcess.PhysApprox.B3GramSum
public import BlockBand.SourceProcess.PhysApprox.B3CovWord
public import BlockBand.SourceProcess.PhysApprox.B3CovLayer
public import BlockBand.SourceProcess.PhysApprox.B3BirthPAssembly
public import BlockBand.SourceProcess.PhysApprox.B3BirthKClose
public import BlockBand.SourceProcess.PhysApprox.B3GenStep
public import BlockBand.SourceProcess.PhysApprox.B3FourK
public import BlockBand.SourceProcess.PhysApprox.B3MomMax
public import BlockBand.SourceProcess.PhysApprox.B3MartMax
public import BlockBand.SourceProcess.PhysApprox.B3MeanClosed
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSum
public import BlockBand.SourceProcess.PhysApprox.B3GramStep
public import BlockBand.SourceProcess.PhysApprox.B3DecayDrift
public import BlockBand.SourceProcess.PhysApprox.B3DecayStep
public import BlockBand.SourceProcess.PhysApprox.B3StepBridge
public import BlockBand.SourceProcess.PhysApprox.B3StopTailMain
public import BlockBand.SourceProcess.PhysApprox.B3CurMain
public import BlockBand.SourceProcess.PhysApprox.B3FddMain
public import BlockBand.SourceProcess.PhysApprox.B3RieszCorr
public import BlockBand.SourceProcess.PhysApprox.B3Bridges
public import BlockBand.SourceProcess.PhysApprox.ClosingBCF
public import BlockBand.SourceProcess.PhysApprox.ClosingGram
public import BlockBand.SourceProcess.PhysApprox.ClosingK
public import BlockBand.SourceProcess.PhysApprox.ConjSym
public import BlockBand.SourceProcess.ContractingWords.WordsHolds

/-!
# A reduced final assembly

**`complexPhysicalApproximationFreq_reduced`**: the frequent-`h` physical approximation from the
contract hypotheses, `KolmogorovConjugate` and twenty further hypotheses. The intermediate
statements (defined in other modules) and the results that give them:

* `TargetT1`–`TargetT4` by `t1`–`t4`; the current `ComplexClosedCurrent` by
  `B3Cur.complexClosedCurrent_holds`; feasibility by `complexClosedFeasible_holds`;
* tightness `ComplexClosedTight` by `StopTail.complexClosedTight_of_summed` (the maximal stopped
  `𝒦` moment, the six halves of `ComplexClosedSummed`, Lindeberg);
* `TargetCapFdd` by `Fdd.targetCapFdd_holds` (itself `complexCapFdd_of_all ∘
  targetCapFddAll_holds`); the limit passage goes through `targetCapCond'_of_targets` with the
  hypothesis `TargetCapIdent`;
* `ClosedKMeanInput` and `ClosedJetHalf` at `Xcl = b3ClosedX` by `closedKMeanInput_of_b3ClosedX` and
  `closedJetHalf_of_b3ClosedX`;
* the maximal stopped `𝒦` moment by `complexKStoppedMomentMax_of_parts`, with the per-length
  `ComplexKCorrMoment` as a hypothesis (this avoids a circular dependency).

**The twenty further hypotheses:** `TargetCapIdent`; `B3ClosedContrStepMean`,
`B3ClosedContrStepFluct`, `B3ClosedContrBound`, `B3ClosedGramLayerMean`, `B3ClosedKLayerMean`;
`CovWordRep e Z`, `ConjWordRep e Z`, `CovErrMoments e`, `CovDecayHyp Z`; `ComplexBirthGramDiag`,
`ComplexBirthCrossGram`; `BirthKFarIn`, `BirthKFarOut`, `BirthKResIn`, `BirthKResOut`;
`ClosedKStepForm b3ClosedX`, `ClosedJetL4Fam b3ClosedX`; `ClosedGramStepFourAt`;
`ComplexKCorrMoment`.

**`complexPhysicalApproximationFreq_reduced_trace`**: the same with `ClosedTraceFour` in place of
`ComplexKCorrMoment` (`complexKCorrMoment_of_closedTrace` and `RawTag.rawTagMoments_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly**: `ComplexPhysicalApproximationFreq` from the input hypotheses,
`KolmogorovConjugate` and the twenty hypotheses listed in the module docstring. -/
theorem complexPhysicalApproximationFreq_reduced (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hId : TargetCapIdent)
    (hSM : B3ClosedContrStepMean) (hSF : B3ClosedContrStepFluct) (hBd : B3ClosedContrBound)
    (hGLM : B3ClosedGramLayerMean) (hKLM : B3ClosedKLayerMean)
    {e Z : CovField} (hCW : CovWordRep e Z) (hJW : ConjWordRep e Z) (hEM : CovErrMoments e)
    (hDec : CovDecayHyp Z)
    (hGDiag : ComplexBirthGramDiag) (hCross : ComplexBirthCrossGram)
    (hFI : BirthKFarIn) (hFO : BirthKFarOut) (hRI : BirthKResIn) (hRO : BirthKResOut)
    (hXF : ClosedKStepForm b3ClosedX) (hXJ : ClosedJetL4Fam b3ClosedX)
    (hGS : ClosedGramStepFourAt) (hCorr : ComplexKCorrMoment) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_b3ClosedX hXJ)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_b3ClosedX hXF hXJ
  have hDec' := b3ClosedContrDecay_of_steps hSM hSF hBd
  have hOld := complexBirthOldL2_of_gramStep hGA hLp hSR hMT hKA hGS
  have hLC := ContractingWords.layerCov_holds hGA hLp hP
  have hCL := covLayerHyp_of_rep hLC hCW
  have hJL := conjLayerHyp_of_rep hLC hJW
  have hGD : GenReqGramDrift := genReqGramDrift_of_decay hDec' hGLM
  have hGB : GenReqGramBracket :=
    genReqGramBracket_of_step (gramSumStepBracket_of_layer hCL hEM hDec)
  have hB : GenReqBirth := genReqBirth_of_baseContracts hMT hGA hLp hSR hOld hGDiag
    (complexBirthKClosing_of_parts hFI hFO hRI hRO) hCross
  have hKD : KDriftSummed := kDriftSummed_of_decay hDec' hKLM
  have hKB : KBracketSummed := kBracketSummed_of_step (kStepBracket_of_layer hCL hEM hDec)
  have hKC : KConjSummed := kConjSummed_of_step (kStepConj_of_layer hJL hEM hDec)
  have hLind : ComplexClosedLindeberg :=
    complexClosedLindeberg_of_gramStep hGA hLp hSR hMT hKA hGS
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_parts
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean) (kStopBirthSum_of_baseContracts hGA hLp hSR hMT hCorr)
  have hS := complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (targetCapCond'_of_targets Fdd.targetCapFdd_holds hId complexClosedFeasible_holds)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

/-- **The reduced final assembly with `ClosedTraceFour`** in place of `ComplexKCorrMoment`
(`complexKCorrMoment_of_closedTrace`). -/
theorem complexPhysicalApproximationFreq_reduced_trace (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hId : TargetCapIdent)
    (hSM : B3ClosedContrStepMean) (hSF : B3ClosedContrStepFluct) (hBd : B3ClosedContrBound)
    (hGLM : B3ClosedGramLayerMean) (hKLM : B3ClosedKLayerMean)
    {e Z : CovField} (hCW : CovWordRep e Z) (hJW : ConjWordRep e Z) (hEM : CovErrMoments e)
    (hDec : CovDecayHyp Z)
    (hGDiag : ComplexBirthGramDiag) (hCross : ComplexBirthCrossGram)
    (hFI : BirthKFarIn) (hFO : BirthKFarOut) (hRI : BirthKResIn) (hRO : BirthKResOut)
    (hXF : ClosedKStepForm b3ClosedX) (hXJ : ClosedJetL4Fam b3ClosedX)
    (hGS : ClosedGramStepFourAt) (hTr : ClosedTraceFour) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_reduced hMT hGA hSR hLp hP hK hId hSM hSF hBd hGLM hKLM
    hCW hJW hEM hDec hGDiag hCross hFI hFO hRI hRO hXF hXJ hGS
    (complexKCorrMoment_of_closedTrace hTr (RawTag.rawTagMoments_holds hGA hLp hSR hMT))

end BlockBand.SourceProcess.PhysApprox.B3
