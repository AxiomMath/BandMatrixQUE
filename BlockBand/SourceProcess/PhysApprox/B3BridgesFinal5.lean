module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal4
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubPlug
public import BlockBand.SourceProcess.PhysApprox.B3BoundJet
public import BlockBand.SourceProcess.PhysApprox.B3BoundJet1
public import BlockBand.SourceProcess.PhysApprox.B3BoundJetDecay

/-!
# A reduced final assembly, fifth version

* Births: `genReqBirth_of_closedBirth_jet` (the newborn diagonal from the closed jet), so
  `ComplexBirthKClosing` is not a hypothesis;
* bounded orders (`complexPhysicalApproximationFreq_reduced5_B`): the jets at orders `≤ 4` with
  the hypothesis `FarFracTraceMoments4`: `closedJet0FamLe_of_frac4`, `closedJetHalf_of_famLe`,
  `closedKMeanInput_of_famLe`, `closedJetStopSmall_of_famLe` (into
  `closedGramStepFourSmall_of_closed`), `b3ClosedContrDecayLe_of_frac4`,
  `covDecayHyp_b3CovZ_of_le`, `genReqGramDrift_of_decayLe`, `kDriftSummed_of_decayLe`.

**`complexPhysicalApproximationFreq_reduced5`** (jets of every order `p`), further hypotheses
(7): `CapIdentGramGen`, `CapIdentKDoubleGen`, `ClosedShiftDiscTrace`, `FarFracTraceMoments`,
`B3CayleyChain`, `B3CayleySep`, `B3ClosedChainNearPin`.

**`complexPhysicalApproximationFreq_reduced5_B`** (bounded orders), further hypotheses (7):
`CapIdentGramGen`, `CapIdentKDoubleGen`, `ClosedShiftDiscTrace`, `FarFracTraceMoments4`,
`B3CayleyChain`, `B3CayleySep`, `B3ClosedChainNearPin`; and three hypotheses (statements defined in
other modules) for the consumers that have no bounded-order form here:
* `ClosedJet0Lp`, `ClosedJet1Lp` (every `p`; on the alive set), the inputs of
  `b3ClosedGramLayerMean_of_chain`, `b3ClosedKLayerMean_of_jet` (order 6) and of
  `covErrMoments_b3CovErr` (`CovErrMoments`, every order);
* `ComplexBirthKDiag`, the output of `complexBirthKDiag_of_jet`, which takes the whole-space
  `∀ p` family `ClosedJet0Fam` although its proof uses `p = 1` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, fifth version** (∀ `p` jets): `ComplexPhysicalApproximationFreq`
from the input hypotheses, `KolmogorovConjugate` and the seven hypotheses listed in the module
docstring. -/
theorem complexPhysicalApproximationFreq_reduced5 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hA : Jet.ClosedShiftDiscTrace) (hFr : Jet.FarFracTraceMoments)
    (hCay : B3CayleyChain) (hSep : B3CayleySep) (hNear : B3ClosedChainNearPin) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hJ0 : ClosedJet0Fam := Jet.closedJet0Fam_of_disc hMT hGA hLp hA hFr
  have hJ01 : ClosedJet0Lp ∧ ClosedJet1Lp :=
    Jet1.closedJets_of_nbhd hMT hGA hLp Jet.closedInputPassive_b3ClosedX
      Jet.closedInputRecursion_b3ClosedX (Jet.closedJetShiftNbhdLp_of_frac hA hFr)
  have h0 : ClosedJet0Lp := hJ01.1
  have h1 : ClosedJet1Lp := hJ01.2
  have hXF : ClosedKStepForm b3ClosedX := closedKStepForm_holds
  have hXJ : ClosedJetL4Fam b3ClosedX := closedJetL4Fam_of_fam hJ0
  have hCh : B3ClosedChainPin := b3ClosedChainPin_of_cayley hCay
  have hg : ClosedCondLp := closedCondLp_of_chain hCh
  have hI : B3DecayIn.B3ClosedContrLayerForm := b3ClosedContrLayerForm_of_cayley hGA hCay hSep
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_b3ClosedX hXJ)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_b3ClosedX hXF hXJ
  have hDec' : B3ClosedContrDecay :=
    B3DecayIn.b3ClosedContrDecay_of_gaussianInputs hGA hLp hI (b3ClosedJetLp_of_fam hJ0 h1 hg hXF)
  have hEM : CovErrMoments b3CovErr := covErrMoments_b3CovErr_of_fam hJ0 h1 hg
  have hDec : CovDecayHyp b3CovZ := covDecayHyp_b3CovZ hDec'
  have hLK : CovLayerHypK b3CovErr b3CovZ := covLayerHypK_of_nearG hGA hLp hP hNear
  have hCL : CovLayerHyp b3CovErr b3CovZ := covLayerHyp_of_chain hGA hLp hP hCh hLK
  have hJL : ConjLayerHyp b3CovErr b3CovZ := conjLayerHyp_holds hGA hLp hP
  have hGLM : B3ClosedGramLayerMean := b3ClosedGramLayerMean_of_chain hGA hLp hP hCh h0 h1 hg
  have hKLM : B3ClosedKLayerMean := b3ClosedKLayerMean_of_jet hGA hLp h0
  have hSm : ClosedGramStepFourSmall :=
    closedGramStepFourSmall_of_update hGA hLp closedGramUpdate_holds hJ0
  have hGD : GenReqGramDrift := genReqGramDrift_of_decay hDec' hGLM
  have hGB : GenReqGramBracket :=
    genReqGramBracket_of_step (gramSumStepBracket_of_layer hCL hEM hDec)
  have hB : GenReqBirth :=
    genReqBirth_of_closedBirth_jet hMT hGA hLp hSR hKA hSm (complexBirthGramDiag_holds hMT hGA) hJ0
  have hKD : KDriftSummed := kDriftSummed_of_decay hDec' hKLM
  have hKB : KBracketSummed := kBracketSummed_of_step (kStepBracket_of_layer hCL hEM hDec)
  have hKC : KConjSummed := kConjSummed_of_step (kStepConj_of_layer hJL hEM hDec)
  have hLind : ComplexClosedLindeberg :=
    complexClosedLindeberg_of_small hGA hLp hSR hMT hKA hSm
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_kdiag hGA hLp
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean)
  have hS := complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (IdentGram.targetCapCond'_of_gen Ident2.capIdentEntrance_holds hGr hKDd
      Ident2.capIdentKStop_holds)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

/-- **The fifth version at bounded orders** (`FarFracTraceMoments4`), with the unbounded consumer
inputs `ClosedJet0Lp`, `ClosedJet1Lp`, `ComplexBirthKDiag` as explicit hypotheses. -/
theorem complexPhysicalApproximationFreq_reduced5_B (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hA : Jet.ClosedShiftDiscTrace) (hB4 : FarFracTraceMoments4)
    (hCay : B3CayleyChain) (hSep : B3CayleySep) (hNear : B3ClosedChainNearPin)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hKDiag : ComplexBirthKDiag) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hJle : ClosedJet0FamLe 4 := closedJet0FamLe_of_frac4 hMT hGA hLp hA hB4
  have hXF : ClosedKStepForm b3ClosedX := closedKStepForm_holds
  have hCh : B3ClosedChainPin := b3ClosedChainPin_of_cayley hCay
  have hg : ClosedCondLp := closedCondLp_of_chain hCh
  have hI : B3DecayIn.B3ClosedContrLayerForm := b3ClosedContrLayerForm_of_cayley hGA hCay hSep
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_famLe hJle)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_famLe hJle
  have hDecLe : B3ClosedContrDecayLe 4 :=
    b3ClosedContrDecayLe_of_frac4 hMT hGA hLp hI hA hB4 (closedCondLpLe_of hg 4)
  have hEM : CovErrMoments b3CovErr := covErrMoments_b3CovErr h0 h1 hg
  have hDec : CovDecayHyp b3CovZ := covDecayHyp_b3CovZ_of_le hDecLe
  have hLK : CovLayerHypK b3CovErr b3CovZ := covLayerHypK_of_nearG hGA hLp hP hNear
  have hCL : CovLayerHyp b3CovErr b3CovZ := covLayerHyp_of_chain hGA hLp hP hCh hLK
  have hJL : ConjLayerHyp b3CovErr b3CovZ := conjLayerHyp_holds hGA hLp hP
  have hGLM : B3ClosedGramLayerMean := b3ClosedGramLayerMean_of_chain hGA hLp hP hCh h0 h1 hg
  have hKLM : B3ClosedKLayerMean := b3ClosedKLayerMean_of_jet hGA hLp h0
  have hSm : ClosedGramStepFourSmall :=
    closedGramStepFourSmall_of_closed hGA hLp closedGramUpdate_holds closedNearVBound_holds
      closedLeakBound_holds (closedJetStopSmall_of_famLe hJle)
  have hGD : GenReqGramDrift := genReqGramDrift_of_decayLe hDecLe hGLM
  have hGB : GenReqGramBracket :=
    genReqGramBracket_of_step (gramSumStepBracket_of_layer hCL hEM hDec)
  have hB : GenReqBirth :=
    genReqBirth_of_closedBirth hMT hGA hLp hSR hKA hSm (complexBirthGramDiag_holds hMT hGA) hKDiag
  have hKD : KDriftSummed := kDriftSummed_of_decayLe hDecLe hKLM
  have hKB : KBracketSummed := kBracketSummed_of_step (kStepBracket_of_layer hCL hEM hDec)
  have hKC : KConjSummed := kConjSummed_of_step (kStepConj_of_layer hJL hEM hDec)
  have hLind : ComplexClosedLindeberg :=
    complexClosedLindeberg_of_small hGA hLp hSR hMT hKA hSm
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_kdiag hGA hLp
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean)
  have hS := complexClosedSummed_of_parts hGD hGB hB hKD hKB hKC
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (IdentGram.targetCapCond'_of_gen Ident2.capIdentEntrance_holds hGr hKDd
      Ident2.capIdentKStop_holds)
    hGD hGB hB hKD hKB hKC hT hKm B3Cur.complexClosedCurrent_holds hLind

end BlockBand.SourceProcess.PhysApprox.B3
