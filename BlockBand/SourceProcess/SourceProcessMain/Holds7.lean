module

public import BlockBand.SourceProcess.SourceProcessMain.Holds6
public import BlockBand.SourceProcess.ClosedReduce.Reduce

/-!
# The source process theorem from `CapCondLimit`

`sourceProcessContract_of_capCond`: `SourceProcessContract` follows from the matched-traces,
Gaussian layer and scalar recursion hypotheses together with `ClosedReduce.CapCondLimit`, which
implies `ClosedIdent.ClosedLimitIdentification`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- From the input hypotheses and `CapCondLimit`. -/
theorem sourceProcessContract_of_capCond (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hC : ClosedReduce.CapCondLimit) : SourceProcessContract :=
  sourceProcessContract_of_closedLimit hMT hGA hLp hP hSR
    (ClosedReduce.closedLimitIdentification_of_capCond
      (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hC)

end BlockBand.SourceProcess.SourceProcessMain
