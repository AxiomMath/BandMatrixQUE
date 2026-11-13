module

public import BlockBand.Endpoints.EndpointsFinalWindow
public import BlockBand.Endpoints.Response.DiffusionAdapters

/-!
# The critical endpoints theorem with the diffusion inputs discharged

We prove `endpoints_of_contracts` by composing `endpoints_of_windowMeas` with
`lifetimeBridgeStatement_holds` and `bridgeOccupationMeasStatement_holds`, which supply
`LifetimeBridgeStatement` and `BridgeOccupationMeasStatement`. The other hypotheses are those of
`endpoints_of_windowMeas`, in the same order, and the conclusion is the same.
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

/-- **The critical endpoints theorem**, from the input statements and the PSSS `SourceContract`:
`endpoints_of_windowMeas` with `LifetimeBridgeStatement` and
`BridgeOccupationMeasStatement` supplied by `lifetimeBridgeStatement_holds` and
`bridgeOccupationMeasStatement_holds`.
-/
theorem endpoints_of_contracts
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
    (hGen : FullSourceGeneratorContract) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_windowMeas hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall
    source hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT
    hCS hReg hL hCP hMT hSmallBall hBirthU hStopsU hCWU hK hPL hTL hPC hPSM hECM hPM hOM hPSC
    hCW hStops hGen lifetimeBridgeStatement_holds bridgeOccupationMeasStatement_holds

end BlockBand.Endpoints
