module

public import BlockBand.SourceProcess.PhysApprox.B3StepK
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh

/-!
# The joint law `ClosedPastFreshLaw`

`closedPastFreshLaw_holds`: under `closedLaw`, the past at a step, the probes with the phase, and
the fresh layer of that step are independent, i.e. `ClosedPastFreshLaw` holds (by
`closedLaw_map_past_fresh`).
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3

/-- The closed law splits as past ⊗ probes/phase ⊗ fresh layer (fresh-layer Fubini). -/
theorem closedPastFreshLaw_holds : ClosedPastFreshLaw :=
  fun b W np i => closedLaw_map_past_fresh b W np i

end BlockBand.SourceProcess.PhysApprox.B3
