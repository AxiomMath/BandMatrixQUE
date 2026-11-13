module

public import BlockBand.Transmission.EnergyUniform.Window
public import BlockBand.SourceProcess.FullSource.SqClock
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# Energy-uniform full-source moments from the transmission inputs

Hypotheses `GaussianAbsorptionContract`, `GaussianLpGradient` and `ScalarRecursionContract`.

`fullSourceMomentsBulk_holds` and `fullSourceMomentsEnergyUniform_holds`: the bulk and the
energy-uniform full-source moment bounds (`FullSourceMomentsBulk`,
`FullSourceMomentsEnergyUniformContract`) hold. The first is `fullSourceMomentsBulk_of_estimates`
with `fullSourceEstimates_holds`; the second follows by the window lemma
`fullSourceMomentsEnergyUniform_of_bulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.EnergyUniform

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.SourceProcess.FullSource

/-- `FullSourceMomentsBulk` from the input hypotheses. -/
theorem fullSourceMomentsBulk_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : FullSourceMomentsBulk :=
  fullSourceMomentsBulk_of_estimates (fullSourceEstimates_holds hGA hLp) hGA hLp hSR

/-- **The `FullSourceMomentsEnergyUniformContract`** from `GaussianAbsorptionContract`,
`GaussianLpGradient` and `ScalarRecursionContract`.
-/
theorem fullSourceMomentsEnergyUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) :
    FullSourceMomentsEnergyUniformContract :=
  fullSourceMomentsEnergyUniform_of_bulk (fullSourceMomentsBulk_holds hGA hLp hSR)

end BlockBand.Transmission.EnergyUniform
