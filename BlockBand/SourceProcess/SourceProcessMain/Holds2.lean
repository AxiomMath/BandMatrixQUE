module

public import BlockBand.SourceProcess.SourceProcessMain.Holds4
public import BlockBand.SourceProcess.HorizonExt.Holds
public import BlockBand.SourceProcess.Sampling.Holds

/-!
# The source process theorem from two hypotheses

`sourceProcessContract_of_two` derives `SourceProcessContract` from the matched-traces, Gaussian
layer and scalar recursion hypotheses together with the following hypotheses (statements defined
in other modules):
* `CutoffLimit.CoupledCutoffFrames` (gives `ModelExists` and `CutoffRemoval`);
* `SourcePins.PhysicalApproximationFreq` (closing and identification).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.SourcePins

/-- `SourceProcessContract` from the input hypotheses, `CoupledCutoffFrames` and
`PhysicalApproximationFreq`. -/
theorem sourceProcessContract_of_two (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hCF : CutoffLimit.CoupledCutoffFrames)
    (hE2 : PhysicalApproximationFreq) : SourceProcessContract :=
  sourceProcessContract_of_four hMT hGA hLp hP hSR hCF HorizonExt.gramHorizonExtension_holds
    (Sampling.physicalSamplingWeak_holds hGA hLp hSR) hE2

end BlockBand.SourceProcess.SourceProcessMain
