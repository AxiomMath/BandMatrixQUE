module

public import BlockBand.Endpoints.Normalization.OneBlockPalmReal
public import BlockBand.Endpoints.Normalization.ZUpper
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Constructor of `OneBlockPalmContract`

We assemble `Clocks.OneBlockPalmContract`, the one-block corollary of the exact-Palm proposition,
field by field (the seven fields of the structure):
* `splitting_exists`, `frame_exists`: from the characteristic function of the physical law and a
  Householder frame;
* `mass`, `index`: from the fixed-exterior one-block coarea formula, the reconstruction and its
  regularity;
* `massReal`, `indexReal`: the signed forms;
* `upper`: `oneBlockPalm_upper_of`, from `FreshEigenpairDensityContract` (field `palm`) and
  `NativeInputs.psss`.

Measures: the exact physical law `model.law`; every one-block splitting law `Pω`; Lebesgue `de`;
`projectiveHaar`; `GUE_{W-1}(c/W)`. Exact identities (no error term), every admissible `p`, model,
block, frame; `upper` uniform as stated in the contract.

`oneBlockPalmContract_of` keeps `FreshEigenpairDensityContract` as a hypothesis (used only by
`upper`). `oneBlockPalmContract_holds` discharges it with
`BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds`, so its only assumption is the
native-inputs argument (only the `psss` field is used, by `upper`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks

/-- `OneBlockPalmContract` from `FreshEigenpairDensityContract` (used only by `upper`) and the
PSSS input `External.NativeInputs`.
-/
theorem oneBlockPalmContract_of (inputs : BlockBand.External.NativeInputs.{0})
    (hD : FreshEigenpairDensityContract) : OneBlockPalmContract where
  splitting_exists := oneBlockPalm_splitting_exists
  frame_exists := oneBlockPalm_frame_exists
  mass := oneBlockPalm_mass
  massReal := oneBlockPalm_massReal
  index := oneBlockPalm_index
  indexReal := oneBlockPalm_indexReal
  upper := oneBlockPalm_upper_of inputs hD

/-- **`OneBlockPalmContract`**, every field: the only hypothesis is the PSSS input
`External.NativeInputs` (`psss` field, used by `upper`); `FreshEigenpairDensityContract` is
supplied by `freshEigenpairDensityContract_holds`.
-/
theorem oneBlockPalmContract_holds (inputs : BlockBand.External.NativeInputs.{0}) :
    OneBlockPalmContract :=
  oneBlockPalmContract_of inputs BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds

end BlockBand.Endpoints.Normalization
