module

public import BlockBand.SourceProcess.PhysApprox.B3KDiagBirth
public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal3

/-!
# The maximal stopped `𝒦` moment with the direct birth sum

* **`complexKStoppedMomentMax_of_kdiag`**: `ComplexKStoppedMomentMax` from `KStopMartMax`,
  `KStopMeanSum` and `kStopBirthSum_holds`, with no per-length stopped moment, no
  `ComplexKCorrMoment` and no `ClosedTraceFour`.
* **`complexPhysicalApproximationFreq_reduced3_kdiag`**: `complexPhysicalApproximationFreq_reduced3`
  with the hypothesis `ClosedTraceFour` removed: the same contract hypotheses, `hK` and the other
  **13** hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **`ComplexKStoppedMomentMax` with the direct birth sum.** -/
theorem complexKStoppedMomentMax_of_kdiag (hGA : Layers.GaussianAbsorptionContract)
    (hLp : Inputs.GaussianLpGradient) (hM : KStopMartMax) (hE : KStopMeanSum) :
    ComplexKStoppedMomentMax :=
  complexKStoppedMomentMax_of_parts hM hE (KDiag.kStopBirthSum_holds hGA hLp)

/-- **The reduced final assembly without `ClosedTraceFour`**: `ComplexPhysicalApproximationFreq`
from the input hypotheses, `KolmogorovConjugate` and the hypotheses of
`complexPhysicalApproximationFreq_reduced3` other than `ClosedTraceFour`. -/
theorem complexPhysicalApproximationFreq_reduced3_kdiag (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hEnt : Ident2.CapIdentEntrance) (hGr : IdentGram.CapIdentGramOff)
    (hKDd : IdentGram.CapIdentKDoubleOff) (hKS : Ident2.CapIdentKStop)
    (hI : B3DecayIn.B3ClosedContrLayerForm) (hJ0 : ClosedJet0Fam) (h1 : ClosedJet1Lp)
    (hCay : B3CayleyChain) (hKLM : B3ClosedKLayerMean)
    (hLK : CovLayerHypK b3CovErr b3CovZ) (hJL : ConjLayerHyp b3CovErr b3CovZ)
    (hRI : BirthKSub.BirthKResInPath) (hGS : ClosedGramStepFourAt) :
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
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_kdiag hGA hLp
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean)
  have hS := complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (IdentGram.targetCapCond'_of_off hEnt hGr hKDd hKS)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

end BlockBand.SourceProcess.PhysApprox.B3

