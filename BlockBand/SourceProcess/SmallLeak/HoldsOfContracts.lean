module

public import BlockBand.SourceProcess.SmallLeak.Holds
public import BlockBand.SourceProcess.SmallLeak.LeakHolds

/-!
# Small channel leakage

`smallChannelLeakage_holds'`: `SmallChannelLeakage` follows from the matched-traces, Gaussian layer
and scalar recursion hypotheses alone. The three steps are supplied by `omittedFluxStart_holds`,
`omittedFluxGrowth_holds` and `leakRecursion_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.SourceProcess.Closing

/-- **`SmallChannelLeakage`** (the small channel leakage) from the five input hypotheses. -/
theorem smallChannelLeakage_holds' (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) : SmallChannelLeakage :=
  smallChannelLeakage_holds hMT hGA hLp hP (omittedFluxGrowth_holds hGA hLp hSR)
    (leakRecursion_holds hMT hGA hLp hSR)

end BlockBand.SourceProcess.SmallLeak
