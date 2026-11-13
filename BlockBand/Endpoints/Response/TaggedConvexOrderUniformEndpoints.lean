module

public import BlockBand.Endpoints.Response.TaggedConvexOrderUniform
public import BlockBand.Endpoints.Sine.FlowAdmissionPalmCorollary
public import BlockBand.Endpoints.EndpointsFinalPalm

/-!
# Consequences of `LmfTaggedFlat` without the tagged-flat hypothesis

With `LmfTaggedFlat` supplied by `lmfTaggedFlat_of_uniformContracts`:
* `localMassFlat_of_uniformContracts`: the local mass flatness theorem (from
  `localMassFlat_of_contracts`);
* `sineEndpoint_of_uniformContracts`: the sine endpoint theorem (from `sineEndpoint_of_taggedFlat'`,
  which already supplies `FaShiftedMassPalm` from `CoareaContract`);
* `endpoints_of_openInputsPalmUniform`: the critical endpoints of every critical family (from
  `endpoints_of_openInputsPalm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory
open BlockBand.Internal.Contracts.Clocks (PhysicalLeadProfileContract NegativeClockContract)
open BlockBand.Internal.Contracts.WindowAngular
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.External.PSSS (SourceContract)

/-- **The local mass flatness theorem** from the contracts in the signature
(`localMassFlat_of_contracts` with `LmfTaggedFlat` from `lmfTaggedFlat_of_uniformContracts`).
-/
theorem localMassFlat_of_uniformContracts (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hUnifMom : FullSourceMomentsEnergyUniformContract)
    (hBirthU : TagBirthValueEnergyUniformContract) (hStopsU : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCWU : ContractingWordsEnergyUniformContract) :
    LocalMassFlatStatement :=
  localMassFlat_of_contracts hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT hNeg hSmall hDens
    (lmfTaggedFlat_of_uniformContracts hUnifMom hBirthU hStopsU hCount hCWU)

/-- **The sine endpoint theorem** from the contracts in the signature
(`sineEndpoint_of_taggedFlat'` with `LmfTaggedFlat` from `lmfTaggedFlat_of_uniformContracts`).
-/
theorem sineEndpoint_of_uniformContracts (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hPhysCount : PhysicalBlockConditionalCount)
    (hExact : ExactPalmContract) (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hUnifMom : FullSourceMomentsEnergyUniformContract)
    (hBirthU : TagBirthValueEnergyUniformContract) (hStopsU : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCWU : ContractingWordsEnergyUniformContract) :
    SineEndpointStatement :=
  sineEndpoint_of_taggedFlat' hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT
    hCS hReg hL hCP hMT hNeg hSmall hDens
    (lmfTaggedFlat_of_uniformContracts hUnifMom hBirthU hStopsU hCount hCWU)

/-- **The critical endpoints of every critical family**, from the hypotheses of
`endpoints_of_openInputsPalm` (with the energy-uniform contracts `TagBirthValueEnergyUniformContract`,
`FullSourceStopsEnergyUniformContract`, `ContractingWordsEnergyUniformContract`), the PSSS
`SourceContract`, `PeSameVolumeLogError`, `LifetimeBridgeStatement` and
`BridgeOccupationStatement`; `LmfTaggedFlat` is supplied by `lmfTaggedFlat_of_uniformContracts`.
The last two hypotheses are jointly inconsistent
(`not_bridgeOccupationStatement_of_lifetimeBridge`), so this form is vacuous.
-/
theorem endpoints_of_openInputsPalmUniform
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
    (hOcc : BridgeOccupationStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputsPalm hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source
    hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT hCS hReg
    hL hCP hMT hSmallBall (lmfTaggedFlat_of_uniformContracts hUnifMom hBirthU hStopsU hCount hCWU)
    hSV hLB hOcc

end BlockBand.Endpoints
