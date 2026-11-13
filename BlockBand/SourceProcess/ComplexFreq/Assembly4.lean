module

public import BlockBand.SourceProcess.ComplexFreq.Assembly3
public import BlockBand.SourceProcess.ComplexCoupled.Holds

/-!
# `ComplexSourceLawContract` from the inputs and the frequent approximation

With `CoupledComplexCutoff` proved (`ComplexCoupled.coupledComplexCutoff_holds`):
* `complexCutoffRemoval_of_baseContracts`: `ComplexCutoffRemoval` from the matched-traces and Gaussian
  inputs alone;
* `complexSourceLawContract_of_physFreq`: `ComplexSourceLawContract` from the matched-traces,
  Gaussian and scalar-recursion inputs and the single hypothesis
  `ComplexPhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexFreq

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`ComplexCutoffRemoval`** from the input hypotheses. -/
theorem complexCutoffRemoval_of_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ComplexConstruct.ComplexCutoffRemoval :=
  complexCutoffRemoval_of_coupled hMT hGA hLp hP ComplexCoupled.coupledComplexCutoff_holds

/-- **The `ComplexSourceLawContract`** from the input hypotheses and
`ComplexPhysicalApproximationFreq`.
-/
theorem complexSourceLawContract_of_physFreq (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hPA : ComplexPhysicalApproximationFreq) :
    ComplexSourceLawContract :=
  complexSourceLawContract_of_two hMT hGA hLp hP hSR ComplexCoupled.coupledComplexCutoff_holds hPA

end BlockBand.SourceProcess.ComplexFreq
