module

public import BlockBand.Internal.Contracts.TransmissionUniform3
public import BlockBand.Transmission.SourceMixingBulk.OneStepMean
public import BlockBand.Transmission.LengthUniform.BulkMassLayer
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# Energy-uniform passive source mixing

Hypotheses `GaussianAbsorptionContract` and `GaussianLpGradient`.

`passiveSourceMixingEnergyUniform_holds`: the one-step mean and fluctuation bounds of the passive
source mixing hold uniformly on the bulk. Both fields come from bulk-uniform theorems applied to
`passiveBounds_holds hGA hLp : PassiveBoundsStatement`: the mean from `oneStepMean_bulk`, the
fluctuation from `oneStepFluctuation_bulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.MixingEnergyUniform

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform3
open scoped Matrix.Norms.L2Operator

/-- **The energy-uniform `PassiveSourceMixingEnergyUniformContract`** from
`GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem passiveSourceMixingEnergyUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : PassiveSourceMixingEnergyUniformContract where
  oneStepMean b hb0 hb κ hκ := by
    obtain ⟨C, W₀, -, hC⟩ := SourceMixingBulk.oneStepMean_bulk
      (PassiveLayer.passiveBounds_holds hGA hLp) hb0 hb hκ
    exact ⟨C, W₀, hC⟩
  oneStepFluctuation b hb0 hb κ hκ p hp :=
    LengthUniform.oneStepFluctuation_bulk (PassiveLayer.passiveBounds_holds hGA hLp) hb0 hb hκ p hp

end BlockBand.Transmission.MixingEnergyUniform
