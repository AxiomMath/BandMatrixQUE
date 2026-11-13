module

public import BlockBand.Endpoints.EndpointsFinal
public import BlockBand.Endpoints.Sine.FlowAdmissionPalm

/-!
# The critical endpoints theorem without the shifted mass Palm hypothesis

We prove `endpoints_of_openInputsPalm`: `endpoints_of_openInputs` with `FaShiftedMassPalm`
supplied by `faShiftedMassPalm_holds` from `CoareaContract`. Besides the contract hypotheses and the
PSSS `SourceContract`, it assumes:
* `LmfTaggedFlat`, the averaged clause of the tagged convex-order theorem;
* `PeSameVolumeLogError`, the same-volume logarithmic error bound;
* `LifetimeBridgeStatement`;
* `BridgeOccupationStatement`.

The last two are jointly inconsistent (`not_bridgeOccupationStatement_of_lifetimeBridge`); the
version with `BridgeOccupationMeasStatement` is `endpoints_of_openInputsPalmMeas`.
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

/-- **The critical endpoints theorem**, from the input statements, the PSSS `SourceContract`,
`LmfTaggedFlat`, `PeSameVolumeLogError`, `LifetimeBridgeStatement` and
`BridgeOccupationStatement`. It is `endpoints_of_openInputs` with `FaShiftedMassPalm` supplied by
`faShiftedMassPalm_holds hCo`.
-/
theorem endpoints_of_openInputsPalm
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
    (hLB : LifetimeBridgeStatement) (hOcc : BridgeOccupationStatement) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), (-2 < E ∧ E < 2) →
      ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsCriticalFamily b E hb hb' family →
          HasCriticalEndpoints b E hb hb' family :=
  endpoints_of_openInputs hMom hUnifLaw hUnifMom hBdry hLen hCount hLead hNeg hSmall source hDens
    hRing hWegner hExt hCo hPair hPhysCount hExact hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP
    hMT hSmallBall hTag (faShiftedMassPalm_holds hCo) hSV hLB hOcc

end BlockBand.Endpoints
