module

public import BlockBand.Critical.Collar.Density.Regular
public import BlockBand.Critical.Collar.Kernel.RegularMain

/-!
# The collar density bound and the collar kernel from the conditional Schur identity

From `CollarConditionalDensityBound` and the listed hypotheses, `collarDensityStatement_of_conditional`
derives `CollarDensityStatement` and `collarKernel_holds_of_conditional` derives
`CollarKernelContract`, both through the regular clause `collarDensityRegular_of_conditional`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical

/-- `CollarDensityStatement` from the conditional Schur identity `CollarConditionalDensityBound`,
`FreshPalmContract`, `PointDensityContract`, `CommonPortMeanContract`, `TraceMatrixContract` and
`PSSS.SourceContract`. -/
theorem collarDensityStatement_of_conditional (hS : CollarConditionalDensityBound)
    (hP : FreshPalmContract) (hPD : PointDensityContract) (hCM : CommonPortMeanContract)
    (hTM : TraceMatrixContract) (source : BlockBand.External.PSSS.SourceContract.{0}) :
    CollarDensityStatement :=
  collarDensityStatement_of_regular
    (collarDensityRegular_of_conditional hS hP hPD hCM hTM source)

/-- `CollarKernelContract` from the conditional Schur identity and the same hypotheses. -/
theorem collarKernel_holds_of_conditional (hS : CollarConditionalDensityBound)
    (hP : FreshPalmContract) (hPD : PointDensityContract) (hCM : CommonPortMeanContract)
    (hTM : TraceMatrixContract) (source : BlockBand.External.PSSS.SourceContract.{0}) :
    CollarKernelContract :=
  BlockBand.Critical.Collar.Kernel.collarKernel_holds_of_densityRegular
    (collarDensityRegular_of_conditional hS hP hPD hCM hTM source)

end BlockBand.Critical.Collar.Density
