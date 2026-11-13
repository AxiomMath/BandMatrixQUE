module

public import BlockBand.Endpoints.Clock.MovingEnergyChain
public import BlockBand.Endpoints.Clock.DetClockBulk
public import BlockBand.Endpoints.Clock.OpenInputsBUniform

/-!
# The endpoints `NegativeClockContract` and `ClockSmallBallContract`, assembled

Two term-mode composites:
* `negativeClock_of_contracts`: `MovingEnergy.negativeClock_of_bulk` applied to
  * `detClockEvolutionDBulk_of`, which proves `DetClockEvolutionDBulk`;
  * `openInputsMomentsBulk_of`, which proves `OpenInputsMomentsBulk`.
* `clockSmallBall_of_contracts`: `clockSmallBall_of_negativeClock` applied to the above.

The hypotheses are `FullSourceMomentsEnergyUniformContract`,
`TransmissionUniform3.PassiveSourceMixingEnergyUniformContract`, `PassiveSourceMixingContract`
(jet existence only), `GaussianAbsorptionContract`, `TraceMatrixContract`,
`WeightedLayerContract`, `LayersOnePort.OnePortWeightedCovarianceContract`, and the two
statements `PassiveCovarianceEnergyUniformHyp` and `LayersBUniformHyp`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements

namespace MovingEnergy

/-- **The negative-clock theorem** (`NegativeClockContract`) from the hypotheses listed in the
module docstring. -/
theorem negativeClock_of_contracts (hFSM : FullSourceMomentsEnergyUniformContract)
    (hPCU : PassiveCovarianceEnergyUniformHyp) (hB : LayersBUniformHyp)
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract) :
    NegativeClockContract :=
  negativeClock_of_bulk hFSM
    (detClockEvolutionDBulk_of hPCU hPSMU hPSM hGA hWC (openInputsMomentsBulk_of hB hGA hTM hWL))
    (openInputsMomentsBulk_of hB hGA hTM hWL)

/-- **The clock small-ball lemma** (`ClockSmallBallContract`), under the same hypotheses as
`negativeClock_of_contracts`.
-/
theorem clockSmallBall_of_contracts (hFSM : FullSourceMomentsEnergyUniformContract)
    (hPCU : PassiveCovarianceEnergyUniformHyp) (hB : LayersBUniformHyp)
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract) :
    ClockSmallBallContract :=
  clockSmallBall_of_negativeClock
    (negativeClock_of_contracts hFSM hPCU hB hPSMU hPSM hGA hTM hWL hWC)

end MovingEnergy

end BlockBand.Endpoints.Clock
