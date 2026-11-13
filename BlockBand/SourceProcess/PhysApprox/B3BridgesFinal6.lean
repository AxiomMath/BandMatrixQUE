module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal5
public import BlockBand.SourceProcess.PhysApprox.B3BoundCovFinal
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubJetLe
public import BlockBand.SourceProcess.PhysApprox.B3JetDiscPin
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanPadZ
public import BlockBand.SourceProcess.PhysApprox.B3LayerKSepZ
public import BlockBand.SourceProcess.PhysApprox.B3LayerKFormZ

/-!
# A reduced final assembly, sixth version

* **`complexPhysicalApproximationFreq_final_summed`**: `complexPhysicalApproximationFreq_final`
  with the hypothesis `ComplexClosedSummed` (stated in another module) in place of its six halves. The final assembly uses the halves only
  through `complexClosedSummed_of_parts` inside `complexCapCondLimit_of_pins`, so the same
  composition goes through with `ComplexClosedSummed` given directly.
* **`complexPhysicalApproximationFreq_reduced6_z`**: the bounded-order version, with the chain
  inputs explicit.
  * jets: `closedJet0FamLe_of_frac4` (order `≤ 4`, then `ClosedJet0FamLe.mono` to order 1),
    `Jet1.closedJetsLe_of_frac4`, `closedJetHalf_of_famLe`, `closedKMeanInput_of_famLe`,
    `closedJetStopSmall_of_famLe`;
  * decay: `b3ClosedContrDecayLe_of_frac4`, with `closedCondLpLe_of` applied to the
    `ClosedCondLp` proved from the chain;
  * the statement `ComplexClosedSummed`: by `complexClosedSummed_of_chain2_le` (its order-4 layer means, drifts
    and `CovErrMoments2` are internal), with `covLayerHypKG_of_nearG`; the variant
    `complexClosedSummed_of_near2_le` (uniform `FreshDeltaQuadCov`) is not used;
  * birth: `genReqBirth_of_closedBirth_jetLe` (`ClosedJet0FamLe 1`);
  * Gram step: `closedGramStepFourSmall_of_closed` with `closedGramUpdate_holds`,
    `closedNearVBound_holds`, `closedLeakBound_holds`; Lindeberg by
    `complexClosedLindeberg_of_small`;
  * the maximal stopped `𝒦` moment: `complexKStoppedMomentMax_of_kdiag`; tightness:
    `StopTail.complexClosedTight_of_summed`.

  Hypotheses beyond the contract hypotheses and `hK` (5): `CapIdentGramGen`,
  `CapIdentKDoubleGen`, `FarFracTraceMoments4`, `B3PadTransportZ`, `B3ClosedContrLayerForm`.
* **`complexPhysicalApproximationFreq_reduced6`**: `complexPhysicalApproximationFreq_reduced6_z`
  with `b3PadTransportZ_holds` and `b3ClosedContrLayerForm_holds` (which uses
  `b3PadGrowthZ_holds`). Its further hypotheses (3) are `CapIdentGramGen`,
  `CapIdentKDoubleGen` and `FarFracTraceMoments4`.
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

/-- **The final assembly with `ComplexClosedSummed` given directly** (the composition of
`complexPhysicalApproximationFreq_final`, without `complexClosedSummed_of_parts`). -/
theorem complexPhysicalApproximationFreq_final_summed (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (t1 : TargetT1) (t2 : TargetT2) (t3 : TargetT3) (t4 : TargetT4)
    (tCap : TargetCapCond') (hS : ComplexClosedSummed)
    (hT : ComplexClosedTight) (hKm : ComplexKStoppedMomentMax) (hCur : ComplexClosedCurrent)
    (hLind : ComplexClosedLindeberg) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hC : ComplexCapCondLimit :=
    tCap (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
      ClosedReduce.existsTimeSFrame_holds hS hT hKm hCur hLind
  have hStop : ComplexClosedLimitLawStopped :=
    complexClosedLimitLawStopped_of_capCond_baseContracts hMT hGA hLp hP
      ComplexCoupled.complexModelExists_holds' hC
  have hb2 : ComplexClosedLimitIdentification := targetT8Stopped_holds hStop
  have hL := targetTL_holds hMT hGA hSR hLp hP
  exact complexPhysicalApproximationFreq_of_pins
    (t1 hMT hGA hSR hLp hP (t2 hMT hGA hSR hLp hP hK hL) (t3 hMT hGA hSR hLp hP hL (t4 hL)))
    (targetT6_holds hMT hGA hSR hLp hP (targetT7_holds hb2))

/-- **The bounded-order assembly with the phase-`z` chain inputs explicit**:
`ComplexPhysicalApproximationFreq` from the input hypotheses, `KolmogorovConjugate`,
`CapIdentGramGen`, `CapIdentKDoubleGen`, `FarFracTraceMoments4`, `B3PadTransportZ` and
`B3ClosedContrLayerForm`. -/
theorem complexPhysicalApproximationFreq_reduced6_z (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hB4 : FarFracTraceMoments4)
    (hTZ : B3LayerMean.B3PadTransportZ) (hI : B3DecayIn.B3ClosedContrLayerForm) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hA : Jet.ClosedShiftDiscTrace := Jet.closedShiftDiscTrace_holds
  have hJ4 : ClosedJet0FamLe 4 := closedJet0FamLe_of_frac4 hMT hGA hLp hA hB4
  have hJ1 : ClosedJet0FamLe 1 := hJ4.mono (by norm_num)
  have hJ01 : ClosedJet0LpLe 4 ∧ ClosedJet1LpLe 4 := Jet1.closedJetsLe_of_frac4 hMT hGA hLp hA hB4
  have hXF : ClosedKStepForm b3ClosedX := closedKStepForm_holds
  have hCh : B3ClosedChainPin := B3LayerMean.b3ClosedChainPin_of_z hTZ
  have hNear : B3ClosedChainNearPin := B3LayerMean.b3ClosedChainNearPin_of_z hTZ
  have hg : ClosedCondLp := closedCondLp_of_chain hCh
  have hKA : KCorrStepFourAt := kCorrStepFourAt_of_closed hGA hLp hSR hMT
    closedPastFreshLaw_holds hXF (closedJetHalf_of_famLe hJ4)
  have hMean : ClosedKMeanInput := closedKMeanInput_of_famLe hJ4
  have hDecLe : B3ClosedContrDecayLe 4 :=
    b3ClosedContrDecayLe_of_frac4 hMT hGA hLp hI hA hB4 (closedCondLpLe_of hg 4)
  have hSm : ClosedGramStepFourSmall :=
    closedGramStepFourSmall_of_closed hGA hLp closedGramUpdate_holds closedNearVBound_holds
      closedLeakBound_holds (closedJetStopSmall_of_famLe hJ4)
  have hB : GenReqBirth := genReqBirth_of_closedBirth_jetLe hMT hGA hLp hSR hKA hSm
    (complexBirthGramDiag_holds hMT hGA) hJ1
  have hKG : CovLayerHypKG b3CovErr b3CovZ := covLayerHypKG_of_nearG hGA hLp hP hNear
  have hS : ComplexClosedSummed :=
    complexClosedSummed_of_chain2_le hGA hLp hP hB hCh hJ01.1 hJ01.2 hKG hDecLe
  have hLind : ComplexClosedLindeberg :=
    complexClosedLindeberg_of_small hGA hLp hSR hMT hKA hSm
  have hKm : ComplexKStoppedMomentMax := complexKStoppedMomentMax_of_kdiag hGA hLp
    (targetMartMax_holds (kStopStepFour_of_corrAt hGA hLp hSR hMT hKA))
    (kStopMeanSum_of_closed hGA hLp hMean)
  have hT : ComplexClosedTight := StopTail.complexClosedTight_of_summed hKm hS hLind
  exact complexPhysicalApproximationFreq_final_summed hMT hGA hSR hLp hP hK t1 t2 t3 t4
    (IdentGram.targetCapCond'_of_gen Ident2.capIdentEntrance_holds hGr hKDd
      Ident2.capIdentKStop_holds)
    hS hT hKm B3Cur.complexClosedCurrent_holds hLind

/-- **The reduced final assembly, sixth version**: `ComplexPhysicalApproximationFreq` from the
input hypotheses, `KolmogorovConjugate`, `CapIdentGramGen`, `CapIdentKDoubleGen` and
`FarFracTraceMoments4`. -/
theorem complexPhysicalApproximationFreq_reduced6 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen)
    (hB4 : FarFracTraceMoments4) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_reduced6_z hMT hGA hSR hLp hP hK hGr hKDd hB4
    b3PadTransportZ_holds (b3ClosedContrLayerForm_holds hGA)

end BlockBand.SourceProcess.PhysApprox.B3
