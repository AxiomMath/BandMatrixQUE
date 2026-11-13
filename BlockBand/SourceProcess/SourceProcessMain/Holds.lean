module

public import BlockBand.SourceProcess.SourcePins.Holds
public import BlockBand.SourceProcess.BornUnique.Holds
public import BlockBand.SourceProcess.CutoffLimit.Main
public import BlockBand.SourceProcess.RankFree.Main

/-!
# The source process theorem from six hypotheses

`sourceProcessContract_of_open` derives `SourceProcessContract` from the matched-traces, Gaussian
layer and scalar recursion hypotheses together with the following hypotheses (statements defined
in other modules):
* `CutoffLimit.CoupledCutoffFrames` (gives `ModelExists` and, with the layer hypotheses,
  `CutoffRemoval`);
* `BornUnique.BornStoppedLaw`, `BornUnique.BornRestart` (give `ModelUnique`);
* `SourceProcessLaw.CapRemoval`;
* `SourcePins.PhysicalSamplingWeak`, `SourcePins.PhysicalApproximationFreq`.

`RankFreeCoupling` is `RankFree.rankFreeCoupling_holds` (no hypotheses) and `EntranceAtomic` is
proved inside `sourceProcessContract_of_pins'`. The later reductions
`sourceProcessContract_of_four`, `sourceProcessContract_of_two`, `sourceProcessContract_of_three`
and `sourceProcessContract_of_closedLimit` discharge all six hypotheses except
`ClosedIdent.ClosedLimitIdentification`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessMain

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.SourcePins

/-- `SourceProcessContract` from the input hypotheses and the six hypotheses
`CoupledCutoffFrames`, `BornStoppedLaw`, `BornRestart`, `CapRemoval`, `PhysicalSamplingWeak`,
`PhysicalApproximationFreq`. -/
theorem sourceProcessContract_of_open (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hCF : CutoffLimit.CoupledCutoffFrames)
    (hSt : BornUnique.BornStoppedLaw) (hR : BornUnique.BornRestart) (hC : CapRemoval)
    (hE1 : PhysicalSamplingWeak) (hE2 : PhysicalApproximationFreq) : SourceProcessContract :=
  sourceProcessContract_of_pins' hMT hGA hLp hP hSR (CutoffLimit.modelExists_of_coupled hCF)
    (BornUnique.modelUnique_of_pins hSt hR) hC (CutoffLimit.cutoffRemoval_holds hMT hGA hLp hP hCF)
    hE1 hE2 RankFree.rankFreeCoupling_holds

end BlockBand.SourceProcess.SourceProcessMain
