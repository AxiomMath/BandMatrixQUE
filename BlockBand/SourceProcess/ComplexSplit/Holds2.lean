module

public import BlockBand.SourceProcess.ComplexSplit.Holds
public import BlockBand.SourceProcess.ComplexCapLimit.Main
public import BlockBand.SourceProcess.ComplexConstruct.Holds

/-!
# `ComplexCapRemoval` with no hypotheses

* `complexCapRemoval_holds`: `ComplexCapRemoval`, from `complexFiniteUniqueness_holds`
  (`ComplexCapLimit.complexCapRemoval_of_uniqueness`).
* `complexSourceLawContract_of_three`: `ComplexSourceLawContract` from the inputs,
  `BornKExtension`, `ComplexCutoffRemoval` and `ComplexPhysicalApproximation`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSplit

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`ComplexCapRemoval`**, with no hypotheses. -/
theorem complexCapRemoval_holds : ComplexConstruct.ComplexCapRemoval :=
  ComplexCapLimit.complexCapRemoval_of_uniqueness complexFiniteUniqueness_holds

/-- **The `ComplexSourceLawContract`** from the input hypotheses and the three hypotheses
`BornKExtension`, `ComplexCutoffRemoval`, `ComplexPhysicalApproximation`. -/
theorem complexSourceLawContract_of_three (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hK : ComplexConstruct.BornKExtension)
    (hCut : ComplexConstruct.ComplexCutoffRemoval)
    (hPA : ComplexConstruct.ComplexPhysicalApproximation) : ComplexSourceLawContract :=
  ComplexConstruct.complexSourceLawContract_of_kExt hMT hGA hLp hP hSR hK complexCapRemoval_holds
    hCut hPA

end BlockBand.SourceProcess.ComplexSplit
