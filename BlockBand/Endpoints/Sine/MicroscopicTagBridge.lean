module

public import BlockBand.Endpoints.Sine.MicroscopicTagFinal
public import BlockBand.Endpoints.Sine.SineEndpoint

/-!
# Consequences of the microscopic tag comparison

* `lmfMicroscopicTagComparison_of_contracts` proves `LmfMicroscopicTagComparison` from the ring,
  Palm, clock and lead-field contracts;
* `localMassFlat_of_contracts`: `LocalMassFlatStatement` with this hypothesis supplied;
* `sineEndpoint_of_taggedFlat`: `SineEndpointStatement` with this hypothesis supplied.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open BlockBand.Internal.Contracts.Inputs

/-- The microscopic-tag hypothesis `LmfMicroscopicTagComparison` of the local mass flatness
theorem, from the contracts in the signature. -/
theorem lmfMicroscopicTagComparison_of_contracts (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) : LmfMicroscopicTagComparison :=
  microscopicTagComparison_of_contracts hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT hNeg

/-- **The local mass flatness theorem** from `LmfTaggedFlat` and the contracts in the
signature. -/
theorem localMassFlat_of_contracts (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hTag : LmfTaggedFlat) : LocalMassFlatStatement :=
  localMassFlat hNeg hSmall hDens hTag
    (lmfMicroscopicTagComparison_of_contracts hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT
      hNeg)

/-- **The sine endpoint theorem** from `LmfTaggedFlat`, `FaShiftedMassPalm` and the contracts in
the signature. -/
theorem sineEndpoint_of_taggedFlat (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hExact : ExactPalmContract) (hShift : FaShiftedMassPalm) (hRot : RingRotationInvariance)
    (hAtom : VanishingBlockAtom) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hFED : FreshEigenpairDensityContract)
    (hUCT : UniformClockTagsPalmContract) (hCS : ClockCovarianceStabilityContract)
    (hReg : BlockRegularEventContract) (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hTag : LmfTaggedFlat) : SineEndpointStatement :=
  sineEndpoint_of_localMassFlatInputs hExt hCo hPair hCount hExact hShift hNeg hSmall hDens hTag
    (lmfMicroscopicTagComparison_of_contracts hRot hAtom hPalm hNorm hFED hUCT hCS hReg hL hCP hMT
      hNeg)

end BlockBand.Endpoints
