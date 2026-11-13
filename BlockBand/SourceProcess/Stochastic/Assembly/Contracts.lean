module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import BlockBand.SourceProcess.Stochastic.Dyson.Assembly
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Assembly of the stochastic-calculus statements

* `contractA_holds`: the Itô formula `SemimartingaleItoFormula d` and the stopping statement
  `StoppedSemimartingale d` hold in every dimension `d`;
* `dysonBrownianMotion_of_b1_b3`: `DysonBrownianMotion N` follows from non-collision
  (`DysonNonCollision N`) and the conditional angular martingale problem (`DysonAngular N`).
-/

namespace BlockBand.SourceProcess.Stochastic.Assembly
open BlockBand.Internal.Contracts.Transmission

/-- **The Itô formula and the stopping statement for continuous semimartingales.** -/
theorem contractA_holds (d : ℕ) : SemimartingaleItoFormula d ∧ StoppedSemimartingale d :=
  ⟨SemimartingaleIto.semimartingaleItoFormula_holds d, Semimartingale.stoppedSemimartingale_holds d⟩

/-- **Dyson Brownian motion from non-collision and the angular martingale problem**, with the Itô
formula and the stopping statement supplied. -/
theorem dysonBrownianMotion_of_b1_b3 (N : ℕ) (h1 : Dyson.DysonNonCollision N)
    (h3 : Dyson.DysonAngular N) : DysonBrownianMotion N :=
  Dyson.dysonBrownianMotion_of_ito_b1_b3 SemimartingaleIto.semimartingaleItoFormula_holds
    Semimartingale.stoppedSemimartingale_holds N h1 h3

end BlockBand.SourceProcess.Stochastic.Assembly
