module

public import BlockBand.SourceProcess.ComplexFreq.Assembly2
public import BlockBand.SourceProcess.BracketCoupling.Main

/-!
# `ComplexSourceLawContract` from the coupled cutoff models and the frequent approximation

With `StoppedBracketCoupling` proved (`BracketCoupling.stoppedBracketCoupling_holds`):
* `complexCutoffRemoval_of_coupled`: `ComplexCutoffRemoval` from the inputs and
  `CoupledComplexCutoff`;
* `complexSourceLawContract_of_two`: `ComplexSourceLawContract` from the inputs,
  `CoupledComplexCutoff` and `ComplexPhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexFreq

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`ComplexCutoffRemoval`** from the input hypotheses and `CoupledComplexCutoff`. -/
theorem complexCutoffRemoval_of_coupled (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hA : ComplexCutoff.CoupledComplexCutoff) : ComplexConstruct.ComplexCutoffRemoval :=
  ComplexCutoff.complexCutoffRemoval_holds' hMT hGA hLp hP hA
    (BracketDef.stoppedBracketCoupling_of BracketCoupling.stoppedBracketCoupling_holds)

/-- **The `ComplexSourceLawContract`** from the input hypotheses, `CoupledComplexCutoff` and
`ComplexPhysicalApproximationFreq`.
-/
theorem complexSourceLawContract_of_two (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hA : ComplexCutoff.CoupledComplexCutoff)
    (hPA : ComplexPhysicalApproximationFreq) : ComplexSourceLawContract :=
  complexSourceLawContract_of_coupled hMT hGA hLp hP hSR hA BracketCoupling.stoppedBracketCoupling_holds hPA

end BlockBand.SourceProcess.ComplexFreq
