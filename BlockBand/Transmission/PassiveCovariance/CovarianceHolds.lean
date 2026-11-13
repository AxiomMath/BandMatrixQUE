module

public import BlockBand.Transmission.PassiveCovariance.M4Near
public import BlockBand.Transmission.PassiveCovariance.AlpReduction

/-!
# The passive covariance lemma

`passiveCovariance_holds`: `PassiveCovarianceContract` holds under `GaussianAbsorptionContract`,
`GaussianLpGradient` and `GaussianPoincare`, from the mean bounds `alpNear_holds` and
`alpINear_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission

/-- **The passive covariance lemma** (`PassiveCovarianceContract`) from
`GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`. -/
theorem passiveCovariance_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : PassiveCovarianceContract :=
  passiveCovariance_holds_of_alp hGA hLp hP
    (alpNear_holds (PassiveLayer.passiveBounds_holds hGA hLp))
    (alpINear_holds (PassiveLayer.passiveBounds_holds hGA hLp))

end BlockBand.Transmission.PassiveCovariance
