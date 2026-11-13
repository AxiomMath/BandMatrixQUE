module

public import BlockBand.SourceProcess.PhysApprox.B3FeasMain
public import BlockBand.SourceProcess.PhysApprox.B3LimDefs

/-!
# Feasibility of the closed Gram process

`complexClosedFeasible_holds`: the closed Gram process is feasible on the cap event at every
length `j ≥ n_s`, that is, `ComplexClosedFeasible` holds.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3

/-- **The closed Gram process is feasible** on the cap event at every length `j ≥ n_s`. -/
theorem complexClosedFeasible_holds : ComplexClosedFeasible :=
  fun _b _E _np _τ _m _T _s _h _K _Vs hD => B3Feas.ae_b3ClosedGram_feasible hD

end BlockBand.SourceProcess.PhysApprox.B3
