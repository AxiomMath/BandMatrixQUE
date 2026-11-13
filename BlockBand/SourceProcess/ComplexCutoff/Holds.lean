module

public import BlockBand.SourceProcess.ComplexCutoff.Main
public import BlockBand.SourceProcess.ComplexCutoff.BracketPin

/-!
# `ComplexCutoffRemoval` from the coupled cutoff models and the stopped bracket coupling

`complexCutoffRemoval_holds'` derives `ComplexCutoffRemoval` from `MatchedTracesContract`, the
Gaussian inputs, `CoupledComplexCutoff` and `StoppedBracketCoupling` (through
`extendedRankFreeCoupling_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open BlockBand.SourceProcess.ComplexConstruct
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs

/-- **`ComplexCutoffRemoval`** from the input hypotheses, `CoupledComplexCutoff` and
`StoppedBracketCoupling`.
-/
theorem complexCutoffRemoval_holds' (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hA : CoupledComplexCutoff) (hS : StoppedBracketCoupling) : ComplexCutoffRemoval :=
  complexCutoffRemoval_holds hMT hGA hLp hP hA (extendedRankFreeCoupling_of hS)

end BlockBand.SourceProcess.ComplexCutoff
