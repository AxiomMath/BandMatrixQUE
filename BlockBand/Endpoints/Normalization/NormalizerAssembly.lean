module

public import BlockBand.Endpoints.Normalization.Normalizer
public import BlockBand.Endpoints.Normalization.RegularEventNative
public import BlockBand.Endpoints.Normalization.ZUpper
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Constructors of `NormalizerContract` and `OneBlockNormalizerContract`

We assemble `Clocks.NormalizerContract` (the normalizer theorem) and its one-block version
`Clocks.OneBlockNormalizerContract` from the following results, all proved in other modules:
* `normalizer_of` and `oneBlockNormalizer_of`;
* the regular events `pairRegularEvent_of_native` and `blockRegularEvent_of_native`, from
  `MatchedTracesContract` and the PSSS input;
* the `upper` clauses `exactPalm_upper_of` and `oneBlockPalm_upper_of`;
* `FreshPalm.freshEigenpairDensityContract_holds`.

The hypotheses are `NativeInputs` (only its `psss` field is used) and the contracts
`Layers.MatchedTracesContract` and `Critical.PointDensityContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical

/-- **The normalizer theorem** (`NormalizerContract`), from `NativeInputs`, `MatchedTracesContract`
and `PointDensityContract`.
-/
theorem normalizerContract_of (inputs : BlockBand.External.NativeInputs.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) : NormalizerContract :=
  normalizer_of (pairRegularEvent_of_native hMT inputs) hPD
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
    (exactPalm_upper_of inputs BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds)

/-- **The one-block normalizer theorem** (`OneBlockNormalizerContract`) from the same inputs. -/
theorem oneBlockNormalizerContract_of (inputs : BlockBand.External.NativeInputs.{0})
    (hMT : MatchedTracesContract) (hPD : PointDensityContract) : OneBlockNormalizerContract :=
  oneBlockNormalizer_of (blockRegularEvent_of_native hMT inputs) hPD
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
    (oneBlockPalm_upper_of inputs BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds)

end BlockBand.Endpoints.Normalization
