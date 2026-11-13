module

public import BlockBand.SourceProcess.ClosedSumProof.TightMain
public import BlockBand.SourceProcess.ClosedSumProof.SummedSplit
public import BlockBand.SourceProcess.ClosedSumProof.Lindeberg

/-!
# `ClosedTight` from `ClosedSummed`, `ClosedFourth` and `ClosedStopTail`

This file imports `closedTight_of` (tightness of the closed Gram process from the summed errors,
the fourth moments and the stop tail), the splitting of `ClosedSummed` into its drift, bracket and
birth parts, and the equivalence of `ClosedFourth` with `ClosedLindeberg`.
-/

set_option autoImplicit false

@[expose] public section
