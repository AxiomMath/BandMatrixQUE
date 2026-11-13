module

public import BlockBand.SourceProcess.PhysApprox.B3KDiagAssembly
public import BlockBand.SourceProcess.PhysApprox.B3Ident2EntrMain
public import BlockBand.SourceProcess.PhysApprox.B3Ident2KStopFin
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramGen
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramKGen
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCurrent
public import BlockBand.SourceProcess.PhysApprox.B3CovRepKBound
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJointG
public import BlockBand.SourceProcess.PhysApprox.B3LayerKMean
public import BlockBand.SourceProcess.PhysApprox.B3LayerKForm
public import BlockBand.SourceProcess.PhysApprox.B3GramUpd
public import BlockBand.SourceProcess.PhysApprox.B3GramStepBounds
public import BlockBand.SourceProcess.PhysApprox.B3GramStepSmall
public import BlockBand.SourceProcess.PhysApprox.B3GramStepBirth
public import BlockBand.SourceProcess.PhysApprox.B3JetClosing
public import BlockBand.SourceProcess.PhysApprox.B3JetPass
public import BlockBand.SourceProcess.PhysApprox.B3JetRecur
public import BlockBand.SourceProcess.PhysApprox.B3JetNbhd
public import BlockBand.SourceProcess.PhysApprox.B3Jet1ShiftJet
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanInv
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanCayley
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanSep

/-!
# A reduced final assembly, fourth version

The ingredients:

* identification: `Ident2.capIdentEntrance_holds`, `Ident2.capIdentKStop_holds`, and
  `IdentGram.targetCapCond'_of_gen` with the hypotheses `CapIdentGramGen`, `CapIdentKDoubleGen`;
* the maximal stopped `𝒦` moment: `complexKStoppedMomentMax_of_kdiag` (through
  `kStopBirthSum_holds`; no `ClosedTraceFour`);
* covariance: `conjLayerHyp_holds`; `CovLayerHypK b3CovErr b3CovZ` from `covLayerHypK_of_nearG`
  (hypothesis `B3ClosedChainNearPin`); `CovLayerHyp` from `covLayerHyp_of_chain`;
* layer means: `b3ClosedKLayerMean_of_jet`, `b3ClosedGramLayerMean_of_chain`;
* Gram step, at the weak rate: `closedGramUpdate_holds`, then
  `closedGramStepFourSmall_of_update`, `complexClosedLindeberg_of_small` and
  `genReqBirth_of_small` (no `ComplexBirthOldL2`, no `ClosedGramStepFourAt`);
  `genReqBirth_of_small` uses `ComplexBirthKClosing`, kept as a hypothesis;
* jets: `Jet.closedJet0Fam_of_disc`; `Jet1.closedJets_of_nbhd` with
  `Jet.closedInputPassive_b3ClosedX`, `Jet.closedInputRecursion_b3ClosedX` and
  `Jet.closedJetShiftNbhdLp_of_frac` (the `∀ p` form of `FarFracTraceMoments`);
* chain, in abstract form (hypotheses `B3CayleyChain`, `B3CayleySep`):
  `b3ClosedChainPin_of_cayley`, `b3ClosedContrLayerForm_of_cayley`.

**`complexPhysicalApproximationFreq_reduced4`**, further hypotheses (8): `CapIdentGramGen`,
`CapIdentKDoubleGen`, `ComplexBirthKClosing`, `ClosedShiftDiscTrace`, `FarFracTraceMoments`,
`B3CayleyChain`, `B3CayleySep`, `B3ClosedChainNearPin`.

**`complexPhysicalApproximationFreq_reduced4_pad`**: the pad witness of the chain,
`B3CayleyChain` from `b3CayleyChain_of_zeroDet` and `B3CayleySep` from `b3CayleySep_of_pad`
(`b3PadInvertible_of_zeroDet`). Further hypotheses (9): `CapIdentGramGen`,
`CapIdentKDoubleGen`, `ComplexBirthKClosing`, `ClosedShiftDiscTrace`, `FarFracTraceMoments`,
`B3PadZeroDet`, `B3PadTransport`, `B3PadGrowth`, `B3ClosedChainNearPin`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, fourth version** (chain inputs abstract):
`ComplexPhysicalApproximationFreq` from the input hypotheses, `KolmogorovConjugate` and the eight
hypotheses listed in the module docstring. -/
theorem complexPhysicalApproximationFreq_reduced4 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hKCl : ComplexBirthKClosing)
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
    genReqBirth_of_small hMT hGA hLp hSR hKA hSm (complexBirthGramDiag_holds hMT hGA) hKCl
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

/-- **The fourth version with the pad witness** of the chain: nine hypotheses beyond the
input hypotheses and `KolmogorovConjugate`. -/
theorem complexPhysicalApproximationFreq_reduced4_pad (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hKCl : ComplexBirthKClosing)
    (hA : Jet.ClosedShiftDiscTrace) (hFr : Jet.FarFracTraceMoments)
    (h0 : B3LayerMean.B3PadZeroDet) (hTr : B3LayerMean.B3PadTransport)
    (hGw : B3LayerMean.B3PadGrowth) (hNear : B3ClosedChainNearPin) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_reduced4 hMT hGA hSR hLp hP hK hGr hKDd hKCl hA hFr
    (B3LayerMean.b3CayleyChain_of_zeroDet h0 hTr)
    (B3LayerMean.b3CayleySep_of_pad (B3LayerMean.b3PadInvertible_of_zeroDet h0) hGw) hNear

end BlockBand.SourceProcess.PhysApprox.B3
