module

public import BlockBand.Transmission.PassiveCovariance.MeansMatch
public import BlockBand.Transmission.PassiveCovariance.GamNear

/-!
# The passive covariance from the two families of means `alpFam`, `alpFamI`

If the means of the word families `alpFam` and `alpFamI` are close to their leading values
(`MeanNear`), then the means match their main terms and the passive covariance statement holds.

* **`meansMatchMain_of_alp hA hα hQ : MeansMatchMain`**;
* `passiveCovariance_holds_of_alp`: `PassiveCovarianceContract` under the input hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission

theorem meansMatchMain_of_alp (hA : PassiveLayer.PassiveBoundsStatement)
    (hα : MeanNear alpFam leadAlp) (hQ : MeanNear alpFamI leadAlpI) : MeansMatchMain :=
  meansMatchMain_of_near hA (tauNear_holds hA) (gamNear_holds hA) hα hQ

theorem passiveCovariance_holds_of_alp (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hα : MeanNear alpFam leadAlp)
    (hQ : MeanNear alpFamI leadAlpI) : PassiveCovarianceContract :=
  passiveCovariance_holds_of_match hGA hLp hP
    (meansMatchMain_of_alp (PassiveLayer.passiveBounds_holds hGA hLp) hα hQ)

end BlockBand.Transmission.PassiveCovariance
