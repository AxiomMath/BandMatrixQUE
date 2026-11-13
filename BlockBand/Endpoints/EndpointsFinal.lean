module

public import BlockBand.Endpoints.EndpointsAssembly
public import BlockBand.Endpoints.EndpointsVarianceMark
public import BlockBand.Endpoints.EndpointsVarianceStationary
public import BlockBand.Endpoints.EndpointsVarianceRotation
public import BlockBand.Endpoints.Response.NonzeroResponse

/-!
# The critical endpoints theorem with the variance hypotheses discharged

We prove `endpoints_of_openInputs`, the conclusion of `endpoints_of_taggedFlat` with:
* `EpMarkStatisticLimit` supplied by `epMarkStatisticLimit_of_lead`;
* `EpStationaryWeightFree` supplied by `epStationaryWeightFree_holds`;
* `EpRotationFourierDiagonal` supplied by `epRotationFourierDiagonal_holds`;
* `EpNonzeroResponse` supplied by `nonzeroResponse hBdry hLB hOcc` (`NonzeroResponseStatement` is
  definitionally `EpNonzeroResponse`).
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
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.External.PSSS (SourceContract)

theorem epv_nonzeroResponse_iff : EpNonzeroResponse ↔ NonzeroResponseStatement := Iff.rfl

/-- **The critical endpoints theorem** (`HasCriticalEndpoints` for every critical family), from
the input statements `ExternalSine`, `PhysicalBlockConditionalCount`, `ConditionalBlockGUECount`,
`CriticalDensity`, `RingBlockModels`, `ProjectedWegner`, `RingRotationInvariance`,
`VanishingBlockAtom`, `MatchedTracesContract`, `CoareaContract`, `FreshEigenpairDensityContract`,
`SmallCriticalContract`, `FullSourceMomentsContract`, `TransmissionLawEnergyUniformContract`,
`FullSourceMomentsEnergyUniformContract`, `DualBoundaryStartContract`,
`TransmissionLengthUniformContract`, `PairRegularEventContract`, `ExactPalmContract`,
`OneBlockPalmContract`, `OneBlockNormalizerContract`, `UniformClockTagsPalmContract`,
`ClockCovarianceStabilityContract`, `BlockRegularEventContract`,
`LeadFieldIdentificationContract`, `UniformClockTagsCommonPortContract`, `NegativeClockContract`,
`ClockSmallBallContract`, `PhysicalLeadProfileContract`, the PSSS `SourceContract`, and
`LmfTaggedFlat`, `FaShiftedMassPalm`, `PeSameVolumeLogError`, `LifetimeBridgeStatement` (proved as
`lifetimeBridgeStatement_holds`) and `BridgeOccupationStatement` (the inputs of `nonzeroResponse`).
-/
theorem endpoints_of_openInputs
    
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
    
    (hLB : LifetimeBridgeStatement) (hOcc : BridgeOccupationStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_taggedFlat hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source hDens
    hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP
    hMT hSmallBall hTag hShift hSV (epv_nonzeroResponse_iff.2 (nonzeroResponse hBdry hLB hOcc))
    (epMarkStatisticLimit_of_lead hLead) epStationaryWeightFree_holds
    epRotationFourierDiagonal_holds

end BlockBand.Endpoints
