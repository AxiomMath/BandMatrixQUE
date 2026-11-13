module

public import BlockBand.Endpoints.Normalization.ExactPalmReal
public import BlockBand.Endpoints.Normalization.ZUpper
public import BlockBand.Coarea.CoareaContract
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Constructor of `ExactPalmContract`

We assemble the five fields of the structure `Clocks.ExactPalmContract` (the exact-Palm proposition):
* `mass`, `index`: from `CoareaContract`;
* `massReal`, `indexReal`: from `CoareaContract`;
* `upper`: from `FreshEigenpairDensityContract` and `NativeInputs.psss`.

`exactPalmContract_of` keeps the two contracts as hypotheses. `exactPalmContract_holds` discharges
them with `BlockBand.Coarea.coareaContract_holds` and
`BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds`, so its only assumption is the
native-inputs argument, of which only the `psss` field is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks

/-- `ExactPalmContract` from `CoareaContract`, `FreshEigenpairDensityContract` and the PSSS inputs
`External.NativeInputs`. -/
theorem exactPalmContract_of (inputs : BlockBand.External.NativeInputs.{0})
    (hC : CoareaContract) (hD : FreshEigenpairDensityContract) : ExactPalmContract where
  mass := exactPalm_mass_of_coarea hC
  massReal := exactPalm_massReal_of_coarea hC
  index := exactPalm_index_of_coarea hC
  indexReal := exactPalm_indexReal_of_coarea hC
  upper := exactPalm_upper_of inputs hD

/-- **`ExactPalmContract`**, with the PSSS inputs `External.NativeInputs` as the only hypothesis
(the two coarea contracts are supplied by `coareaContract_holds` and
`freshEigenpairDensityContract_holds`). -/
theorem exactPalmContract_holds (inputs : BlockBand.External.NativeInputs.{0}) :
    ExactPalmContract :=
  exactPalmContract_of inputs BlockBand.Coarea.coareaContract_holds
    BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds

end BlockBand.Endpoints.Normalization
