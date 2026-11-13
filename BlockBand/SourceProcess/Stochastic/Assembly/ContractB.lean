module
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularHolds
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Dyson Brownian motion at `β = 2`

`contractB_holds`: `DysonBrownianMotion N` holds for every `N`, i.e. the eigenvalues of a
Hermitian Brownian motion started at a Hermitian matrix form a Dyson Brownian motion.
-/

namespace BlockBand.SourceProcess.Stochastic.Assembly
open BlockBand.Internal.Contracts.Transmission

/-- **Dyson Brownian motion, `β = 2`.** -/
theorem contractB_holds (N : ℕ) : DysonBrownianMotion N :=
  Dyson.Angular.dysonBrownianMotion_holds N

end BlockBand.SourceProcess.Stochastic.Assembly
