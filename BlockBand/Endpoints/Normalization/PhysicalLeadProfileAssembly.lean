module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyFinal
public import BlockBand.Endpoints.Normalization.LeadGaussianStep
public import BlockBand.Endpoints.Normalization.LeadProfileCommonPort
public import BlockBand.Endpoints.Normalization.LeadProfileRegularityAngular
public import BlockBand.Endpoints.Normalization.LeadProfileRegularitySide
public import BlockBand.Endpoints.Normalization.NormalizerAssembly
public import BlockBand.Endpoints.Normalization.OneBlockPalmAssembly
public import BlockBand.Endpoints.Normalization.RegularEventNative
public import BlockBand.Endpoints.Normalization.GaussianRatiosAssembly
public import BlockBand.Endpoints.Clock.CommonPortRatios
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Constructor of `Clocks.PhysicalLeadProfileContract`

We assemble `Clocks.PhysicalLeadProfileContract` (the physical lead-profile theorem) in
`physicalLeadProfileContract_of`, through `leadGaussianStep_of_oneBlockPalm` and
`physicalLeadProfile_of_gaussian_commonPort`, from the following results of other modules:
* `physicalLeadProfile_of_steps`;
* `leadGaussianStep_of`;
* `leadCommonPortStep_of`;
* `leadAngularRegularity_of_oneBlockPalm`;
* `leadSideMeasurability_holds`;
* `oneBlockPalmContract_holds`;
* `oneBlockNormalizerContract_of`;
* `blockRegularEvent_of_native`;
* `gaussianRatios_of_contracts`;
* `Clock.commonPortRatios_of_commonPortMean`;
* `Coarea.FreshPalm.freshEigenpairDensityContract_holds`.

The hypotheses of `physicalLeadProfileContract_of` are `inputs : External.NativeInputs.{0}`
(only `psss` is used), `Layers.MatchedTracesContract`, `Critical.PointDensityContract`,
`CoareaPalm.FreshPalmContract`, `Critical.CommonPortMeanContract` and `VanishingBlockAtom`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.Critical

/-- **`LeadGaussianStep`** without the `LeadAngularRegularity` argument: that hypothesis is supplied
by `leadAngularRegularity_of_oneBlockPalm` from `OneBlockPalmContract`, already an argument of
`leadGaussianStep_of`. The other hypotheses are `FreshEigenpairDensityContract`,
`GaussianRatiosContract`, `BlockRegularEventContract`, `OneBlockNormalizerContract` and
`VanishingBlockAtom`.
-/
theorem leadGaussianStep_of_oneBlockPalm (hD : FreshEigenpairDensityContract)
    (hGR : GaussianRatiosContract) (hReg : BlockRegularEventContract)
    (hPalm : OneBlockPalmContract) (hNorm : OneBlockNormalizerContract)
    (hVBA : VanishingBlockAtom) : LeadGaussianStep :=
  leadGaussianStep_of hD hGR hReg hPalm hNorm (leadAngularRegularity_of_oneBlockPalm hPalm) hVBA

/-- **The physical lead-profile theorem** from `physicalLeadProfile_of_steps` with its two
regularity hypotheses supplied (`leadAngularRegularity_of_oneBlockPalm`,
`leadSideMeasurability_holds`); the remaining arguments are `OneBlockPalmContract`,
`OneBlockNormalizerContract`, `LeadGaussianStep` and `LeadCommonPortStep`.
-/
theorem physicalLeadProfile_of_gaussian_commonPort (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hLGS : LeadGaussianStep)
    (hLCP : LeadCommonPortStep) : PhysicalLeadProfileContract :=
  physicalLeadProfile_of_steps hPalm hNorm hLGS hLCP
    (leadAngularRegularity_of_oneBlockPalm hPalm) leadSideMeasurability_holds

/-- **Constructor of `Clocks.PhysicalLeadProfileContract`**. Hypotheses:

* `inputs : NativeInputs.{0}`: the cited PSSS inputs; only the `psss` field is used (via
  `oneBlockPalmContract_holds`, `oneBlockNormalizerContract_of`, `blockRegularEvent_of_native`);
* `hMT : MatchedTracesContract`;
* `hPD : PointDensityContract`;
* `hFP : FreshPalmContract`;
* `hCPM : CommonPortMeanContract`;
* `hVBA : VanishingBlockAtom`.

`FreshEigenpairDensityContract` is supplied by `freshEigenpairDensityContract_holds`.
-/
theorem physicalLeadProfileContract_of (inputs : BlockBand.External.NativeInputs.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) (hFP : FreshPalmContract)
    (hCPM : CommonPortMeanContract) (hVBA : VanishingBlockAtom) :
    PhysicalLeadProfileContract :=
  have hD : FreshEigenpairDensityContract :=
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
  have hPalm : OneBlockPalmContract := oneBlockPalmContract_holds inputs
  have hNorm : OneBlockNormalizerContract := oneBlockNormalizerContract_of inputs hMT hPD
  physicalLeadProfile_of_gaussian_commonPort hPalm hNorm
    (leadGaussianStep_of_oneBlockPalm hD (gaussianRatios_of_contracts hFP hPD hD)
      (blockRegularEvent_of_native hMT inputs) hPalm hNorm hVBA)
    (leadCommonPortStep_of
      (BlockBand.Endpoints.Clock.commonPortRatios_of_commonPortMean hCPM) hMT)

end BlockBand.Endpoints.Normalization
