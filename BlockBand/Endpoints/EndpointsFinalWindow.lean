module

public import BlockBand.Endpoints.EndpointsFinalMeas
public import BlockBand.Endpoints.Response.RemoteHigherWindow

/-!
# The critical endpoints theorem with the window-uniform remote-higher bound discharged

We prove `endpoints_of_windowMeas`: `endpoints_of_remoteHigherUniformMeas` with
`RemoteHigherUniformStatement` supplied by `remoteHigherUniform_of_contracts`. Besides contract
hypotheses and the PSSS `SourceContract`, it assumes `LifetimeBridgeStatement` and
`BridgeOccupationMeasStatement`. Relative to `endpoints_of_remoteHigherUniformMeas`, the new
hypotheses are `TransmissionLawContract`, `PassiveCovarianceContract`,
`PassiveSourceMixingContract`, `EdgeClockMomentsContract`, `OnePortPassiveMeanContract`,
`OnePortOperatorMomentsContract`, `PassiveScalarContractionContract`, `ContractingWordsContract`,
`FullSourceStopsContract` and `FullSourceGeneratorContract`.
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
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.External.PSSS (SourceContract)

/-- **The critical endpoints theorem**, from the input statements, the PSSS `SourceContract`,
`LifetimeBridgeStatement` and the measurable occupation statement `BridgeOccupationMeasStatement`.
It is `endpoints_of_remoteHigherUniformMeas` with
`RemoteHigherUniformStatement` supplied by `remoteHigherUniform_of_contracts`.
-/
theorem endpoints_of_windowMeas
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
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hPSC : PassiveScalarContractionContract)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract)
    (hGen : FullSourceGeneratorContract)
    (hLB : LifetimeBridgeStatement) (hOccM : BridgeOccupationMeasStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_remoteHigherUniformMeas hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall
    source hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT
    hCS hReg hL hCP hMT hSmallBall hBirthU hStopsU hCWU hK hPL
    (remoteHigherUniform_of_contracts hCount hTL hPC hPSM hECM hLen hPM hOM hPSC hCW hStops hGen
      hUnifMom)
    hLB hOccM

end BlockBand.Endpoints
