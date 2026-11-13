module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal2
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3JetFam
public import BlockBand.SourceProcess.PhysApprox.B3CovRepGram
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCond
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanGram
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubSym
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramOff

/-!
# The reduced final assembly, third version

`complexPhysicalApproximationFreq_reduced3` updates `complexPhysicalApproximationFreq_reduced2`
with the following reductions:

* ClosedForm: `closedKStepForm_holds : ClosedKStepForm b3ClosedX` (so passivity of `b3ClosedX`
  is free as well);
* JetFam: the one leaf `ClosedJet0Fam` gives `ClosedJet0Lp` (`closedJet0Lp_of_fam`),
  `ClosedJetL4Fam b3ClosedX` (`closedJetL4Fam_of_fam`), `B3ClosedJetLp` (`b3ClosedJetLp_of_fam`)
  and `CovErrMoments b3CovErr` (`covErrMoments_b3CovErr_of_fam`);
* CovRep: the layer hypotheses are used directly,
  `CovLayerHyp b3CovErr b3CovZ` from `covLayerHyp_of_chain` (the input hypotheses, the chain
  hypothesis, `CovLayerHypK`),
  and `ConjLayerHyp b3CovErr b3CovZ` as a leaf; `ClosedCondLp` from `closedCondLp_of_chain`;
* LayerMean: `B3ClosedGramLayerMean` from `b3ClosedGramLayerMean_of_chain`, with the chain hypothesis
  from `b3ClosedChainPin_of_cayley` (leaf `B3CayleyChain`);
* BirthKSub: `complexBirthKClosing_of_far_resIn`, with the far parts proved as `birthKFarIn_holds`
  and `birthKFarOut_holds` and `BirthKResInPath` a hypothesis;
* IdentGram: `IdentGram.targetCapCond'_of_off`, whose off-birth hypotheses
  `CapIdentGramOff`, `CapIdentKDoubleOff` are weaker than `CapIdentGram`, `CapIdentKDouble`.

**Further hypotheses (14):** `CapIdentEntrance`, `CapIdentGramOff`, `CapIdentKDoubleOff`,
`CapIdentKStop`; `B3ClosedContrLayerForm`; `ClosedJet0Fam`; `ClosedJet1Lp`; `B3CayleyChain`;
`B3ClosedKLayerMean`; `CovLayerHypK b3CovErr b3CovZ`; `ConjLayerHyp b3CovErr b3CovZ`;
`BirthKResInPath`; `ClosedGramStepFourAt`; `ClosedTraceFour`; besides the five input hypotheses
and `KolmogorovConjugate`. (`CapIdentEntrance` is proved, as `Ident2.capIdentEntrance_holds`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, third version**: `ComplexPhysicalApproximationFreq` from the
input hypotheses, `KolmogorovConjugate` and 14 further hypotheses. -/
theorem complexPhysicalApproximationFreq_reduced3 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hEnt : Ident2.CapIdentEntrance) (hGr : IdentGram.CapIdentGramOff)
    (hKDd : IdentGram.CapIdentKDoubleOff) (hKS : Ident2.CapIdentKStop)
    (hI : B3DecayIn.B3ClosedContrLayerForm) (hJ0 : ClosedJet0Fam) (h1 : ClosedJet1Lp)
    (hCay : B3CayleyChain) (hKLM : B3ClosedKLayerMean)
    (hLK : CovLayerHypK b3CovErr b3CovZ) (hJL : ConjLayerHyp b3CovErr b3CovZ)
    (hRI : BirthKSub.BirthKResInPath) (hGS : ClosedGramStepFourAt) (hTr : ClosedTraceFour) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hXF : ClosedKStepForm b3ClosedX := closedKStepForm_holds
  have hXJ : ClosedJetL4Fam b3ClosedX := closedJetL4Fam_of_fam hJ0
  have hCh : B3ClosedChainPin := b3ClosedChainPin_of_cayley hCay
  have hg : ClosedCondLp := closedCondLp_of_chain hCh
  have h0 : ClosedJet0Lp := closedJet0Lp_of_fam hJ0
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_b3ClosedX hXJ)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_b3ClosedX hXF hXJ
  have hDec' : B3ClosedContrDecay :=
    B3DecayIn.b3ClosedContrDecay_of_gaussianInputs hGA hLp hI (b3ClosedJetLp_of_fam hJ0 h1 hg hXF)
  have hEM : CovErrMoments b3CovErr := covErrMoments_b3CovErr_of_fam hJ0 h1 hg
  have hDec : CovDecayHyp b3CovZ := covDecayHyp_b3CovZ hDec'
  have hOld := complexBirthOldL2_of_gramStep hGA hLp hSR hMT hKA hGS
  have hCL : CovLayerHyp b3CovErr b3CovZ := covLayerHyp_of_chain hGA hLp hP hCh hLK
  have hGLM : B3ClosedGramLayerMean := b3ClosedGramLayerMean_of_chain hGA hLp hP hCh h0 h1 hg
  have hGD : GenReqGramDrift := genReqGramDrift_of_decay hDec' hGLM
  have hGB : GenReqGramBracket :=
    genReqGramBracket_of_step (gramSumStepBracket_of_layer hCL hEM hDec)
  have hB : GenReqBirth := genReqBirth_of_baseContracts hMT hGA hLp hSR hOld
    (complexBirthGramDiag_holds hMT hGA)
    (BirthKSub.complexBirthKClosing_of_far_resIn (BirthKSub.birthKFarIn_holds hMT hGA)
      (BirthKSub.birthKFarOut_holds hMT hGA) hRI)
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
    (IdentGram.targetCapCond'_of_off hEnt hGr hKDd hKS)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

end BlockBand.SourceProcess.PhysApprox.B3
