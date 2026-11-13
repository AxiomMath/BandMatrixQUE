module

public import BlockBand.SourceProcess.ComplexCoupled.Holds
public import BlockBand.SourceProcess.ComplexCutoff.Holds

/-!
# `ComplexCutoffRemoval` from the Gaussian inputs and `StoppedBracketCoupling`

* `complexCutoffRemoval_of_bracket`: `ComplexCutoffRemoval` from `MatchedTracesContract`, the
  Gaussian inputs and `StoppedBracketCoupling`, using `coupledComplexCutoff_holds`.
* `complexModelExists_holds'`: `ComplexModelExists` with no hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled

open BlockBand.SourceProcess.ComplexConstruct BlockBand.SourceProcess.ComplexCutoff
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs

/-- **`ComplexCutoffRemoval`** from the input hypotheses and `StoppedBracketCoupling`. -/
theorem complexCutoffRemoval_of_bracket (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hS : StoppedBracketCoupling) : ComplexCutoffRemoval :=
  complexCutoffRemoval_holds' hMT hGA hLp hP coupledComplexCutoff_holds hS

/-- **`ComplexModelExists`** with no hypotheses (from `complexModelExists_of_coupled`). -/
theorem complexModelExists_holds' : ComplexModelExists :=
  complexModelExists_of_coupled coupledComplexCutoff_holds

end BlockBand.SourceProcess.ComplexCoupled
