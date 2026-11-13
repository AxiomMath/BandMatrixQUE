module

public import BlockBand.SourceProcess.SmallLeak.Assembly
public import BlockBand.SourceProcess.SmallLeak.FluxStart

/-!
# Small channel leakage from the growth and leakage steps

`smallChannelLeakage_holds`: `SmallChannelLeakage` follows from the matched-traces and Gaussian layer
hypotheses together with `OmittedFluxGrowth` and `LeakRecursion`; the start bound
`OmittedFluxStart` is supplied by `omittedFluxStart_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.SourceProcess.Closing

/-- **`SmallChannelLeakage`** from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`, `GaussianPoincare`, `OmittedFluxGrowth` and `LeakRecursion`. -/
theorem smallChannelLeakage_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hG : OmittedFluxGrowth) (hL : LeakRecursion) : SmallChannelLeakage :=
  smallChannelLeakage_of (omittedFluxStart_holds hMT hGA hLp hP) hG hL

end BlockBand.SourceProcess.SmallLeak
