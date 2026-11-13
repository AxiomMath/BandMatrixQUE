module

public import BlockBand.SourceProcess.SourceProcessMain.Holds5
public import BlockBand.SourceProcess.SmallLeak.HoldsOfContracts

/-!
# The source process theorem from one further hypothesis

`sourceProcessContract_of_closedLimit`: besides the matched-traces, Gaussian layer and scalar
recursion hypotheses, the only hypothesis is `ClosedIdent.ClosedLimitIdentification`
(the existence half of the identification of the closed physical Gram coordinates with the finite
Gram law).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- `SourceProcessContract` from the input hypotheses and `ClosedLimitIdentification`. -/
theorem sourceProcessContract_of_closedLimit (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hCL : ClosedIdent.ClosedLimitIdentification) :
    SourceProcessContract :=
  sourceProcessContract_of_three hMT hGA hLp hP hSR (SmallLeak.omittedFluxGrowth_holds hGA hLp hSR)
    (SmallLeak.leakRecursion_holds hMT hGA hLp hSR) hCL

end BlockBand.SourceProcess.SourceProcessMain
