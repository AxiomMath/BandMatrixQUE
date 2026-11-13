module

public import BlockBand.Endpoints.Clock.MovingEnergyOpenClock
public import BlockBand.Endpoints.Clock.SmallBall

/-!
# The moving-energy clock chain down to `NegativeClockContract`

The proofs here are term-mode composites of results proved in sibling modules:
* `MovingEnergy.openClockLawUniformInitial_of` gives the hypothesis `h1` of the Robin entrance
  lemma from the two compact-set statements;
* `RobinEntrance.robinEntranceLimitUpTo_of` gives the closed-port reduction;
* `RobinEntrance.negativeClock_of_upTo` gives the negative-clock theorem;
* `clockSmallBall_of_negativeClock` gives the clock small-ball lemma.

The hypotheses of `negativeClock_of_bulk` and `clockSmallBall_of_bulk` are
`FullSourceMomentsEnergyUniformContract`, `MovingEnergy.DetClockEvolutionDBulk` and
`MovingEnergy.OpenInputsMomentsBulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.TransmissionUniform

namespace MovingEnergy

/-- **The negative-clock theorem** (`NegativeClockContract`) from
`FullSourceMomentsEnergyUniformContract` and the two compact-set statements
`DetClockEvolutionDBulk`, `OpenInputsMomentsBulk` (proved from further hypotheses as
`detClockEvolutionDBulk_of` and `openInputsMomentsBulk_of`).
-/
theorem negativeClock_of_bulk (hFSM : FullSourceMomentsEnergyUniformContract)
    (hDet : DetClockEvolutionDBulk) (hOI : OpenInputsMomentsBulk) : NegativeClockContract :=
  RobinEntrance.negativeClock_of_upTo hFSM
    (RobinEntrance.robinEntranceLimitUpTo_of (openClockLawUniformInitial_of hDet hOI))

/-- **The clock small-ball lemma** (`ClockSmallBallContract`), through
`clockSmallBall_of_negativeClock`, under the same hypotheses as `negativeClock_of_bulk`.
-/
theorem clockSmallBall_of_bulk (hFSM : FullSourceMomentsEnergyUniformContract)
    (hDet : DetClockEvolutionDBulk) (hOI : OpenInputsMomentsBulk) : ClockSmallBallContract :=
  clockSmallBall_of_negativeClock (negativeClock_of_bulk hFSM hDet hOI)

end MovingEnergy

end BlockBand.Endpoints.Clock
