module

public import BlockBand.Critical.Collar.Density.CondSchurInstance
public import BlockBand.Critical.Collar.Density.CondSchurGeneric
public import BlockBand.Critical.Collar.Density.RegularConsequences

/-!
# The conditional Schur identity for the collar density

* `collarConditionalDensityIdentity_holds : CollarConditionalDensityIdentity`: the equality form of
  the conditional Schur identity, for all `W ≥ 1`, `0 < b < 1/2`, real `e`, Hermitian `X` without
  norm bound, `a₁ ≤ a₂` and `u`;
* `collarConditionalDensityBound_holds`: the upper-bound form that follows from it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical

/-- **The conditional Schur identity**, equality form. -/
theorem collarConditionalDensityIdentity_holds : CollarConditionalDensityIdentity :=
  fun _ hW _ hb0 hb e _ hX _ _ ha u =>
    collarConditionalDensity_eq_of_ae_generic hW hb e hX ha u (ae_csGeneric_collar hW hb0 hb e hX)

/-- The upper-bound form used by `collarDensityRegular_of_conditional`. -/
theorem collarConditionalDensityBound_holds : CollarConditionalDensityBound :=
  collarConditionalDensityIdentity_holds.bound

/-- `CollarDensityStatement` from `FreshPalmContract`, `PointDensityContract`, `CommonPortMeanContract`,
`TraceMatrixContract` and `PSSS.SourceContract`. -/
theorem collarDensityStatement_of_inputs (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : CollarDensityStatement :=
  collarDensityStatement_of_conditional collarConditionalDensityBound_holds hP hPD hCM hTM source

/-- `CollarKernelContract` from the same hypotheses. -/
theorem collarKernelContract_of_inputs (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : CollarKernelContract :=
  collarKernel_holds_of_conditional collarConditionalDensityBound_holds hP hPD hCM hTM source

end BlockBand.Critical.Collar.Density
