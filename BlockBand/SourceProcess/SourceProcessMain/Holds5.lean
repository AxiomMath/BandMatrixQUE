module

public import BlockBand.SourceProcess.SourceProcessMain.Holds2
public import BlockBand.SourceProcess.CoupledFrames.Closes
public import BlockBand.SourceProcess.SmallLeak.Holds
public import BlockBand.SourceProcess.ClosingLeak.Holds
public import BlockBand.SourceProcess.ClosedIdent.LimitPoints

/-!
# The source process theorem from three hypotheses

`PhysicalApproximationFreq` is obtained from `Closing.physicalApproximationFreq_of_split`, fed by
the following results from other modules:
  * `ClosingLeak.closingLeakage_holds` on `SmallLeak.smallChannelLeakage_holds`;
  * `ClosedIdent.closedIdentification_of_limits`.

The hypotheses of `sourceProcessContract_of_three`, besides the matched-traces, Gaussian layer and
scalar recursion hypotheses, are the following statements (defined in other modules):
* `SmallLeak.OmittedFluxGrowth`, `SmallLeak.LeakRecursion` (the small channel leakage; both are
  proved from the input hypotheses, see `sourceProcessContract_of_closedLimit`);
* `ClosedIdent.ClosedLimitIdentification` (the existence half of the identification).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- `SourceProcessContract` from the input hypotheses, `OmittedFluxGrowth`, `LeakRecursion` and
`ClosedLimitIdentification`. -/
theorem sourceProcessContract_of_three (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hG : SmallLeak.OmittedFluxGrowth) (hL : SmallLeak.LeakRecursion)
    (hCL : ClosedIdent.ClosedLimitIdentification) : SourceProcessContract :=
  sourceProcessContract_of_two hMT hGA hLp hP hSR CoupledFrames.coupledCutoffFrames_holds
    (Closing.physicalApproximationFreq_of_split
      (ClosingLeak.closingLeakage_holds hGA hLp hSR
        (SmallLeak.smallChannelLeakage_holds hMT hGA hLp hP hG hL))
      (ClosedIdent.closedIdentification_of_limits hMT hGA hLp hP hCL))

end BlockBand.SourceProcess.SourceProcessMain
