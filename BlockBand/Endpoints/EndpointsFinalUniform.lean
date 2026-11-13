module

public import BlockBand.Endpoints.Response.TaggedConvexOrderUniformEndpoints
public import BlockBand.Endpoints.Poisson.SingleCollarPaths

/-!
# The critical endpoints theorem with the tagged-flat and Ward hypotheses discharged

We prove `endpoints_of_remoteHigherUniform`: `endpoints_of_openInputsPalmUniform` with
`PeSameVolumeLogError` supplied by `peSameVolumeLogError_of_remoteHigher`. Besides the contract
hypotheses (now including `CollarKernelContract` and `PassiveLog`) and the PSSS `SourceContract`, it
assumes `RemoteHigherUniformStatement`, the energy-window-uniform remote-higher bound, and the
diffusion statements `LifetimeBridgeStatement` and `BridgeOccupationStatement`. The last two are
jointly inconsistent; the version with `BridgeOccupationMeasStatement` is
`endpoints_of_remoteHigherUniformMeas`.
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

/-- **The critical endpoints theorem**, from the input statements, the PSSS `SourceContract`,
`RemoteHigherUniformStatement` and the diffusion lemmas `LifetimeBridgeStatement`
and `BridgeOccupationStatement`.
It is `endpoints_of_openInputsPalmUniform` with
`PeSameVolumeLogError` supplied by `peSameVolumeLogError_of_remoteHigher`.
-/
theorem endpoints_of_remoteHigherUniform
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
    (hOcc : BridgeOccupationStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputsPalmUniform hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall
    source hDens hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT
    hCS hReg hL hCP hMT hSmallBall hBirthU hStopsU hCWU
    (peSameVolumeLogError_of_remoteHigher hK hMT hLen hPL hRHU) hLB hOcc

end BlockBand.Endpoints
