module

public import BlockBand.Coarea.CoareaAssembly
public import BlockBand.Coarea.FixedOmegaRegular

/-!
# The coarea theorem

`coareaContract_holds : CoareaContract`, from `coareaContract_of_formulaFixed` and the
fixed-`ω` formula `formula_fixed_of_regularAE` at the almost-sure regularity
`coarea_regular_ae`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Coarea

open BlockBand.Internal.Contracts.CoareaPalm

/-- **The coarea theorem**: `CoareaContract` holds, with no hypothesis. -/
theorem coareaContract_holds : CoareaContract :=
  CoareaAssembly.coareaContract_of_formulaFixed
    (FixedOmega.formula_fixed_of_regularAE RegularAE.coarea_regular_ae)

end BlockBand.Coarea
