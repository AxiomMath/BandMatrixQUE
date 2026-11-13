module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularMain
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionHolds

/-!
# The angular martingale problem and Dyson Brownian motion, unconditionally

* `dysonAngular_holds`: the conditional angular martingale problem `DysonAngular N`, from
  `dysonAngular_of_b1` and non-collision `dysonNonCollision_holds`;
* `Angular.dysonBrownianMotion_holds`: `DysonBrownianMotion N`, via
  `dysonBrownianMotion_of_angular`, i.e. `dysonBrownianMotion_of_ito_b1_b3` with the Itô formula
  and the stopping statement supplied.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.Internal.Contracts.Transmission

/-- **The conditional angular martingale problem `DysonAngular N`**, unconditionally. -/
theorem dysonAngular_holds (N : ℕ) : DysonAngular N :=
  dysonAngular_of_b1 N (dysonNonCollision_holds N)

/-- **Dyson Brownian motion, `DysonBrownianMotion N`**, unconditionally. -/
theorem Angular.dysonBrownianMotion_holds (N : ℕ) : DysonBrownianMotion N :=
  dysonBrownianMotion_of_angular N (dysonAngular_holds N)

end BlockBand.SourceProcess.Stochastic.Dyson
