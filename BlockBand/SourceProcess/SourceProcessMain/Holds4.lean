module

public import BlockBand.SourceProcess.SourceProcessMain.Holds
public import BlockBand.SourceProcess.BornStopped.Main
public import BlockBand.SourceProcess.BornRestart.Holds
public import BlockBand.SourceProcess.CapLimit.Main

/-!
# The source process theorem from four hypotheses

`sourceProcessContract_of_four` derives `SourceProcessContract` from the matched-traces, Gaussian
layer and scalar recursion hypotheses together with the following hypotheses (statements defined
in other modules):
* `CutoffLimit.CoupledCutoffFrames` (gives `ModelExists`, `CutoffRemoval`);
* `BornStopped.GramHorizonExtension` (gives `BornStoppedLaw`, hence `ModelUnique` and `CapRemoval`);
* `SourcePins.PhysicalSamplingWeak`, `SourcePins.PhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.SourcePins

/-- `SourceProcessContract` from the input hypotheses, `CoupledCutoffFrames`,
`GramHorizonExtension`, `PhysicalSamplingWeak` and `PhysicalApproximationFreq`. -/
theorem sourceProcessContract_of_four (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hCF : CutoffLimit.CoupledCutoffFrames)
    (hE : BornStopped.GramHorizonExtension) (hE1 : PhysicalSamplingWeak)
    (hE2 : PhysicalApproximationFreq) : SourceProcessContract :=
  sourceProcessContract_of_open hMT hGA hLp hP hSR hCF (BornStopped.bornStoppedLaw_of_extension hE)
    BornRestart.bornRestart_holds
    (CapLimit.capRemoval_of_pins (BornStopped.bornStoppedLaw_of_extension hE)
      BornRestart.bornRestart_holds) hE1 hE2

end BlockBand.SourceProcess.SourceProcessMain
