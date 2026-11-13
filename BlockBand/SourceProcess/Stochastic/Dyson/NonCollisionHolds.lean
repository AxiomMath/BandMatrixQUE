module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionMain
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract

/-!
# Non-collision of Dyson Brownian motion, unconditionally

`dysonNonCollision_holds`: a.s. the spectrum of `F + G_t` is simple for every `t > 0`.
Consequently `DysonBrownianMotion N` follows from the angular martingale problem alone
(`dysonBrownianMotion_of_angular`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.Internal.Contracts.Transmission

/-- **Non-collision `DysonNonCollision N`**, unconditionally. -/
theorem dysonNonCollision_holds (N : ℕ) : DysonNonCollision N :=
  dysonNonCollision_of_ito SemimartingaleIto.semimartingaleItoFormula_holds
    Semimartingale.stoppedSemimartingale_holds N

/-- `DysonBrownianMotion N` from the angular martingale problem `DysonAngular N` alone. -/
theorem dysonBrownianMotion_of_angular (N : ℕ) (h3 : DysonAngular N) : DysonBrownianMotion N :=
  dysonBrownianMotion_of_ito_b1_b3 SemimartingaleIto.semimartingaleItoFormula_holds
    Semimartingale.stoppedSemimartingale_holds N (dysonNonCollision_holds N) h3

end BlockBand.SourceProcess.Stochastic.Dyson
