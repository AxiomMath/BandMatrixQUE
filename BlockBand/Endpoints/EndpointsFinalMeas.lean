module

public import BlockBand.Endpoints.EndpointsFinalUniform
public import BlockBand.Endpoints.Response.NonzeroResponseMeas

/-!
# The critical endpoints theorem with the measurable bridge-occupation statement

The theorems `endpoints_of_openInputs`, `endpoints_of_openInputsPalm`,
`endpoints_of_openInputsPalmUniform` and `endpoints_of_remoteHigherUniform` take
`LifetimeBridgeStatement` together with `BridgeOccupationStatement`, which are jointly
inconsistent (`not_bridgeOccupationStatement_of_lifetimeBridge`), so they hold vacuously. This file
gives the same theorems with `BridgeOccupationStatement` replaced by the measurable version
`BridgeOccupationMeasStatement`:
* `endpoints_of_openInputsMeas`: `endpoints_of_taggedFlat` with `EpNonzeroResponse` supplied by
  `nonzeroResponse_of_occMeas hBdry hLB hOccM` and the other three variance hypotheses supplied as
  in `endpoints_of_openInputs`;
* `endpoints_of_openInputsPalmMeas`: `FaShiftedMassPalm` from `faShiftedMassPalm_holds hCo`;
* `endpoints_of_openInputsPalmUniformMeas`: `LmfTaggedFlat` from
  `lmfTaggedFlat_of_uniformContracts`;
* `endpoints_of_remoteHigherUniformMeas`: `PeSameVolumeLogError` from
  `peSameVolumeLogError_of_remoteHigher`.

By `bridgeOccupationMeas_of_bridgeOccupation` these hypotheses are no stronger than the original
ones.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory
open BlockBand.Internal.Contracts.Clocks (PhysicalLeadProfileContract NegativeClockContract)
open BlockBand.Internal.Contracts.WindowAngular
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.External.PSSS (SourceContract)

/-- **The critical endpoints theorem with the measurable occupation statement.**
`endpoints_of_openInputs` with `BridgeOccupationStatement` replaced by
`BridgeOccupationMeasStatement`; `EpNonzeroResponse` is supplied by
`nonzeroResponse_of_occMeas hBdry hLB hOccM`. The conclusion is `HasCriticalEndpoints`. -/
theorem endpoints_of_openInputsMeas
    
    (hMom : FullSourceMomentsContract) (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    
    (hSmall : SmallCriticalContract)
    
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner)
    
    (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hPhysCount : PhysicalBlockConditionalCount) (hExact : ExactPalmContract)
    (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hSmallBall : ClockSmallBallContract)
    -- further hypotheses
    (hTag : LmfTaggedFlat) (hShift : FaShiftedMassPalm) (hSV : PeSameVolumeLogError)
    
    (hLB : LifetimeBridgeStatement) (hOccM : BridgeOccupationMeasStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_taggedFlat hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source hDens
    hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP
    hMT hSmallBall hTag hShift hSV
    (epv_nonzeroResponse_iff.2 (nonzeroResponse_of_occMeas hBdry hLB hOccM))
    (epMarkStatisticLimit_of_lead hLead) epStationaryWeightFree_holds
    epRotationFourierDiagonal_holds

/-- **The critical endpoints theorem** without the shifted mass Palm hypothesis, with the measurable
occupation statement:
`endpoints_of_openInputsPalm` with `BridgeOccupationStatement` replaced by
`BridgeOccupationMeasStatement`; `FaShiftedMassPalm` is supplied by `faShiftedMassPalm_holds hCo`. -/
theorem endpoints_of_openInputsPalmMeas
    (hMom : FullSourceMomentsContract) (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hSmall : SmallCriticalContract)
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner)
    (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hPhysCount : PhysicalBlockConditionalCount) (hExact : ExactPalmContract)
    (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hSmallBall : ClockSmallBallContract)
    (hTag : LmfTaggedFlat) (hSV : PeSameVolumeLogError)
    (hLB : LifetimeBridgeStatement) (hOccM : BridgeOccupationMeasStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputsMeas hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source
    hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT hCS hReg
    hL hCP hMT hSmallBall hTag (faShiftedMassPalm_holds hCo) hSV hLB hOccM

/-- **The critical endpoints theorem** with `LmfTaggedFlat` discharged, with the measurable
occupation statement:
`endpoints_of_openInputsPalmUniform` with `BridgeOccupationStatement` replaced by
`BridgeOccupationMeasStatement`; `LmfTaggedFlat` is supplied by
`lmfTaggedFlat_of_uniformContracts`. -/
theorem endpoints_of_openInputsPalmUniformMeas
    (hMom : FullSourceMomentsContract) (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hSmall : SmallCriticalContract)
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner)
    (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hPhysCount : PhysicalBlockConditionalCount) (hExact : ExactPalmContract)
    (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hSmallBall : ClockSmallBallContract)
    (hBirthU : TagBirthValueEnergyUniformContract) (hStopsU : FullSourceStopsEnergyUniformContract)
    (hCWU : ContractingWordsEnergyUniformContract)
    (hSV : PeSameVolumeLogError) (hLB : LifetimeBridgeStatement)
    (hOccM : BridgeOccupationMeasStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputsPalmMeas hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall
    source hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT
    hCS hReg hL hCP hMT hSmallBall
    (lmfTaggedFlat_of_uniformContracts hUnifMom hBirthU hStopsU hCount hCWU) hSV hLB hOccM

/-- **The critical endpoints theorem** with the tagged-flat and Ward hypotheses discharged, with the
measurable occupation statement: `endpoints_of_remoteHigherUniform` with `BridgeOccupationStatement` replaced by
`BridgeOccupationMeasStatement`; `PeSameVolumeLogError` is supplied by
`peSameVolumeLogError_of_remoteHigher`. -/
theorem endpoints_of_remoteHigherUniformMeas
    (hMom : FullSourceMomentsContract) (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount)
    (hLead : PhysicalLeadProfileContract) (hNeg : NegativeClockContract)
    (hSmall : SmallCriticalContract)
    (source : SourceContract.{0}) (hDens : CriticalDensity) (hRing : RingBlockModels)
    (hWegner : ProjectedWegner)
    (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hPhysCount : PhysicalBlockConditionalCount) (hExact : ExactPalmContract)
    (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hSmallBall : ClockSmallBallContract)
    (hBirthU : TagBirthValueEnergyUniformContract) (hStopsU : FullSourceStopsEnergyUniformContract)
    (hCWU : ContractingWordsEnergyUniformContract)
    (hK : CollarKernelContract) (hPL : PassiveLog)
    (hRHU : RemoteHigherUniformStatement) (hLB : LifetimeBridgeStatement)
    (hOccM : BridgeOccupationMeasStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputsPalmUniformMeas hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg
    hSmall source hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED
    hUCT hCS hReg hL hCP hMT hSmallBall hBirthU hStopsU hCWU
    (peSameVolumeLogError_of_remoteHigher hK hMT hLen hPL hRHU) hLB hOccM

end BlockBand.Endpoints
