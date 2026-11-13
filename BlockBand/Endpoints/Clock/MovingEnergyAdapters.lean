module

public import BlockBand.Endpoints.Clock.MovingEnergyEndpoints
public import BlockBand.Internal.Contracts.TransmissionUniform4
public import BlockBand.Internal.Contracts.LayersBUniform

/-!
# The negative-clock and small-ball endpoints from the contracts

Two hypotheses of the moving-energy chain are supplied by contract statements with identical
bodies:
* `passiveCovarianceEnergyUniformHyp_of_contract`:
  `TransmissionUniform4.PassiveCovarianceEnergyUniformContract` gives
  `PassiveCovarianceEnergyUniformHyp` (the bodies are identical, so the adapter is the identity);
* `layersBUniformHyp_of_contracts`: the three contracts
  `LayersBUniform.{GaussianAbsorption,TraceFluctuation,ClockMean}UniformContract` give the three
  fields of `LayersBUniformHyp`, one field each.

Hence `negativeClock_of_uniformContracts` and `clockSmallBall_of_uniformContracts` have the
conclusions of `negativeClock_of_contracts` and `clockSmallBall_of_contracts` (the negative-clock theorem and the
clock small-ball lemma), with `hPCU` and `hB` supplied by these adapters.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements

namespace MovingEnergy

/-- `TransmissionUniform4.PassiveCovarianceEnergyUniformContract` gives
`PassiveCovarianceEnergyUniformHyp` (the bodies are identical).
-/
theorem passiveCovarianceEnergyUniformHyp_of_contract
    (h : BlockBand.Internal.Contracts.TransmissionUniform4.PassiveCovarianceEnergyUniformContract) :
    PassiveCovarianceEnergyUniformHyp := h

/-- The three `LayersBUniform` contracts give `LayersBUniformHyp`, one field each.
-/
theorem layersBUniformHyp_of_contracts
    (hGAU : BlockBand.Internal.Contracts.LayersBUniform.GaussianAbsorptionUniformContract)
    (hTFU : BlockBand.Internal.Contracts.LayersBUniform.TraceFluctuationUniformContract)
    (hCMU : BlockBand.Internal.Contracts.LayersBUniform.ClockMeanUniformContract) :
    LayersBUniformHyp :=
  ⟨hGAU, hTFU, hCMU⟩

/-- **The negative-clock theorem** (`NegativeClockContract`) from contracts only:
`negativeClock_of_contracts` with `PassiveCovarianceEnergyUniformHyp` and `LayersBUniformHyp`
supplied by `passiveCovarianceEnergyUniformHyp_of_contract` and `layersBUniformHyp_of_contracts`.
-/
theorem negativeClock_of_uniformContracts (hFSM : FullSourceMomentsEnergyUniformContract)
    (hPCF : BlockBand.Internal.Contracts.TransmissionUniform4.PassiveCovarianceEnergyUniformContract)
    (hGAU : BlockBand.Internal.Contracts.LayersBUniform.GaussianAbsorptionUniformContract)
    (hTFU : BlockBand.Internal.Contracts.LayersBUniform.TraceFluctuationUniformContract)
    (hCMU : BlockBand.Internal.Contracts.LayersBUniform.ClockMeanUniformContract)
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract) :
    NegativeClockContract :=
  negativeClock_of_contracts hFSM (passiveCovarianceEnergyUniformHyp_of_contract hPCF)
    (layersBUniformHyp_of_contracts hGAU hTFU hCMU) hPSMU hPSM hGA hTM hWL hWC

/-- **The clock small-ball lemma** (`ClockSmallBallContract`) from contracts only, under the same
hypotheses as `negativeClock_of_uniformContracts`.
-/
theorem clockSmallBall_of_uniformContracts (hFSM : FullSourceMomentsEnergyUniformContract)
    (hPCF : BlockBand.Internal.Contracts.TransmissionUniform4.PassiveCovarianceEnergyUniformContract)
    (hGAU : BlockBand.Internal.Contracts.LayersBUniform.GaussianAbsorptionUniformContract)
    (hTFU : BlockBand.Internal.Contracts.LayersBUniform.TraceFluctuationUniformContract)
    (hCMU : BlockBand.Internal.Contracts.LayersBUniform.ClockMeanUniformContract)
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract) :
    ClockSmallBallContract :=
  clockSmallBall_of_contracts hFSM (passiveCovarianceEnergyUniformHyp_of_contract hPCF)
    (layersBUniformHyp_of_contracts hGAU hTFU hCMU) hPSMU hPSM hGA hTM hWL hWC

end MovingEnergy

end BlockBand.Endpoints.Clock
