module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal
public import BlockBand.SourceProcess.PhysApprox.B3BridgesJet
public import BlockBand.SourceProcess.PhysApprox.B3DecayInStep
public import BlockBand.SourceProcess.PhysApprox.B3DecayInBound
public import BlockBand.SourceProcess.PhysApprox.B3CovRepDecay
public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr
public import BlockBand.SourceProcess.PhysApprox.B3BirthMDiag
public import BlockBand.SourceProcess.PhysApprox.B3BirthMOther
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubHolds
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Main

/-!
# A reduced final assembly, second version

**`complexPhysicalApproximationFreq_reduced2`**: the frequent-`h` physical approximation with the
following ingredients.

* Decay: `b3ClosedContrDecay_of_gaussianInputs` (`B3ClosedContrBound` is proved,
  `b3ClosedContrBound_holds`; the inputs are `B3ClosedContrLayerForm` and `B3ClosedJetLp`), with
  `B3ClosedJetLp` from the three closed jets by the jet bridge;
* covariance: the concrete fields `e = b3CovErr`, `Z = b3CovZ`, with `CovErrMoments b3CovErr` from
  the jets (`covErrMoments_b3CovErr`) and `CovDecayHyp b3CovZ` from the decay
  (`covDecayHyp_b3CovZ`);
* births: `complexBirthGramDiag_holds` and `complexBirthCrossGram_holds` (the latter from
  `ComplexBirthOldL2`), and `complexBirthKClosing_of_contracts` (the far birth masses are proved;
  the path-only resolvent estimates are hypotheses);
* the stopped `𝒦` moment: `complexKCorrMoment_of_closedTrace` with `ClosedTraceFour`;
* limit passage: `targetCapCond'_of_identPins` (`TargetCapFddAll` is proved).

**Remaining hypotheses (18):** `CapIdentEntrance`, `CapIdentGram`, `CapIdentKDouble`,
`CapIdentKStop`; `B3ClosedContrLayerForm`; `ClosedJet0Lp`, `ClosedJet1Lp`, `ClosedCondLp`;
`B3ClosedGramLayerMean`, `B3ClosedKLayerMean`; `CovWordRep b3CovErr b3CovZ`,
`ConjWordRep b3CovErr b3CovZ`; `BirthKResInPath`, `BirthKResOutPath`;
`ClosedKStepForm b3ClosedX`, `ClosedJetL4Fam b3ClosedX`; `ClosedGramStepFourAt`;
`ClosedTraceFour`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, second version**: `ComplexPhysicalApproximationFreq` from the
input hypotheses, `KolmogorovConjugate` and the eighteen hypotheses listed in the module
docstring. -/
theorem complexPhysicalApproximationFreq_reduced2 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hEnt : Ident2.CapIdentEntrance) (hGr : Ident2.CapIdentGram)
    (hKDd : Ident2.CapIdentKDouble) (hKS : Ident2.CapIdentKStop)
    (hI : B3DecayIn.B3ClosedContrLayerForm)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp)
    (hGLM : B3ClosedGramLayerMean) (hKLM : B3ClosedKLayerMean)
    (hCW : CovWordRep b3CovErr b3CovZ) (hJW : ConjWordRep b3CovErr b3CovZ)
    (hRI : BirthKSub.BirthKResInPath) (hRO : BirthKSub.BirthKResOutPath)
    (hXF : ClosedKStepForm b3ClosedX) (hXJ : ClosedJetL4Fam b3ClosedX)
    (hGS : ClosedGramStepFourAt) (hTr : ClosedTraceFour) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_b3ClosedX hXJ)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_b3ClosedX hXF hXJ
  have hDec' : B3ClosedContrDecay :=
    B3DecayIn.b3ClosedContrDecay_of_gaussianInputs hGA hLp hI (b3ClosedJetLp_of_jets h0 h1 hg hXF)
  have hEM : CovErrMoments b3CovErr := covErrMoments_b3CovErr h0 h1 hg
  have hDec : CovDecayHyp b3CovZ := covDecayHyp_b3CovZ hDec'
  have hOld := complexBirthOldL2_of_gramStep hGA hLp hSR hMT hKA hGS
  have hLC := ContractingWords.layerCov_holds hGA hLp hP
  have hCL := covLayerHyp_of_rep hLC hCW
  have hJL := conjLayerHyp_of_rep hLC hJW
  have hGD : GenReqGramDrift := genReqGramDrift_of_decay hDec' hGLM
  have hGB : GenReqGramBracket :=
    genReqGramBracket_of_step (gramSumStepBracket_of_layer hCL hEM hDec)
  have hB : GenReqBirth := genReqBirth_of_baseContracts hMT hGA hLp hSR hOld
    (complexBirthGramDiag_holds hMT hGA)
    (BirthKSub.complexBirthKClosing_of_contracts hMT hGA hRI hRO)
    (complexBirthCrossGram_holds hMT hGA hOld)
  have hKD : KDriftSummed := kDriftSummed_of_decay hDec' hKLM
  have hKB : KBracketSummed := kBracketSummed_of_step (kStepBracket_of_layer hCL hEM hDec)
  have hKC : KConjSummed := kConjSummed_of_step (kStepConj_of_layer hJL hEM hDec)
  have hLind : ComplexClosedLindeberg :=
    complexClosedLindeberg_of_gramStep hGA hLp hSR hMT hKA hGS
  have hCorr : ComplexKCorrMoment :=
    complexKCorrMoment_of_closedTrace hTr (RawTag.rawTagMoments_holds hGA hLp hSR hMT)
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_parts
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean) (kStopBirthSum_of_baseContracts hGA hLp hSR hMT hCorr)
  have hS := complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (Ident2.targetCapCond'_of_identPins hEnt hGr hKDd hKS)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

end BlockBand.SourceProcess.PhysApprox.B3
