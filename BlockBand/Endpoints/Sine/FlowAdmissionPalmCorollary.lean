module

public import BlockBand.Endpoints.Sine.FlowAdmissionPalm
public import BlockBand.Endpoints.Sine.FlowAdmissionBridge
public import BlockBand.Endpoints.Sine.MicroscopicTagBridge

/-!
# Flow admission and the sine endpoint without the shifted mass Palm hypothesis

With `FaShiftedMassPalm` supplied by `faShiftedMassPalm_holds`:
* `flowAdmission'`: flow admission from `ExactPalmContract`, `CoareaContract`, the block count and
  the pair clause of local mass flatness;
* `flowAdmission_of_localMassFlat'`: the same with the pair clause from `LocalMassFlatStatement`;
* `sineEndpoint_of_taggedFlat'`: the sine endpoint from the tagged flat bound.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.Inputs

/-- **Flow admission** without the shifted Palm hypothesis: from `ExactPalmContract`,
`CoareaContract`, `PhysicalBlockConditionalCount` and the pair clause `FaLocalMassFlatPair`. -/
theorem flowAdmission' (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hCount : PhysicalBlockConditionalCount) (hLMF : FaLocalMassFlatPair) :
    FlowAdmissionStatement :=
  flowAdmission hPalm hCo (faShiftedMassPalm_holds hCo) hCount hLMF

/-- Flow admission from `LocalMassFlatStatement`, without `FaShiftedMassPalm`. -/
theorem flowAdmission_of_localMassFlat' (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hCount : PhysicalBlockConditionalCount) (hLMF : LocalMassFlatStatement) :
    FlowAdmissionStatement :=
  flowAdmission_of_localMassFlat hPalm hCo (faShiftedMassPalm_holds hCo) hCount hLMF

/-- **The sine endpoint theorem** from `LmfTaggedFlat` and the contracts in the signature
(`FaShiftedMassPalm` of `sineEndpoint_of_taggedFlat` is discharged by `faShiftedMassPalm_holds`). -/
theorem sineEndpoint_of_taggedFlat' (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hExact : ExactPalmContract) (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hTag : LmfTaggedFlat) : SineEndpointStatement :=
  sineEndpoint_of_taggedFlat hExt hCo hPair hCount hExact (faShiftedMassPalm_holds hCo) hRot hAtom
    hPalm hNorm hFED hUCT hCS hReg hL hCP hMT hNeg hSmall hDens hTag

end BlockBand.Endpoints
