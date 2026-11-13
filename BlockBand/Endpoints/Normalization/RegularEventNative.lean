module

public import BlockBand.Endpoints.Normalization.RegularEventAssembly
public import BlockBand.Wegner.PhysicalConditionalCount

/-!
# Regular prior event: constructors from `MatchedTracesContract` and the PSSS input

The hypothesis `Inputs.PhysicalBlockConditionalCount` of `pairRegularEvent_of_inputs` and
`blockRegularEvent_of_inputs` is supplied by `Wegner.physicalBlockConditionalCount_holds` from
the cited input `NativeInputs.psss` (`PSSS.SourceContract.{0}`). The other hypothesis is
`Layers.MatchedTracesContract` (fields `residualPair`, `commonPort`).
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.ClocksCommonPort

/-- `PairRegularEventContract` from `MatchedTracesContract` and the PSSS input. -/
theorem pairRegularEvent_of_native (hMT : MatchedTracesContract)
    (native : BlockBand.External.NativeInputs.{0}) : PairRegularEventContract :=
  pairRegularEvent_of_inputs hMT (BlockBand.Wegner.physicalBlockConditionalCount_holds native.psss)

/-- `BlockRegularEventContract` from `MatchedTracesContract` and the PSSS input. -/
theorem blockRegularEvent_of_native (hMT : MatchedTracesContract)
    (native : BlockBand.External.NativeInputs.{0}) : BlockRegularEventContract :=
  blockRegularEvent_of_inputs hMT (BlockBand.Wegner.physicalBlockConditionalCount_holds native.psss)

end BlockBand.Endpoints.Normalization
