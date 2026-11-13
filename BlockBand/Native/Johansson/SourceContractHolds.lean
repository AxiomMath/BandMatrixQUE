module

public import BlockBand.Native.Johansson.SourceContractAssembly
public import BlockBand.Native.Johansson.CoordinateBridge
public import BlockBand.Native.Johansson.Symmetrization
public import BlockBand.Native.Johansson.KernelFactor
public import BlockBand.Native.Johansson.Gaudin
public import BlockBand.Native.Johansson.ContourKernel

/-!
# Johansson's formula (2.18): `sourceContract_holds`

**`sourceContract_holds : BlockBand.External.Johansson.SourceContract`**, with no hypothesis. It is
`sourceContract_of_statements` applied to the intermediate statements. Only `orderedLaw_holds` is
proved here; the others are cited from sibling modules of `BlockBand.Native.Johansson`:
* `orderedLaw_holds` = `orderedLaw_of_bridge coordinateBridge_holds` (the ordered law);
* `profileNonneg_holds` (positivity of the profile);
* `kernelFactor_holds`, `gaussDetScaling_holds` (factorization);
* `kernelMarginal_holds` (Gaudin marginals);
* `factorialFromOrdered_holds` (factorial measures from the ordered law);
* `contourKernel_holds`, `verticalIntegrable_holds`, `circleIntegrable_holds` (the contour form).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open BlockBand.External.Johansson

/-- **The ordered law** of the Gaussian law `matrixMeasure S d` (no hypothesis). -/
theorem orderedLaw_holds : OrderedLawStatement :=
  orderedLaw_of_bridge coordinateBridge_holds

/-- **Johansson's formula** (eq. (2.18) at `S = t/N`), proved natively with no hypothesis. -/
theorem sourceContract_holds : SourceContract :=
  sourceContract_of_statements orderedLaw_holds profileNonneg_holds kernelFactor_holds
    gaussDetScaling_holds kernelMarginal_holds factorialFromOrdered_holds contourKernel_holds
    verticalIntegrable_holds circleIntegrable_holds

end BlockBand.Native.Johansson
