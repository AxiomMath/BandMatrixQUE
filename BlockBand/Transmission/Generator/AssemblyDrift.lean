module

public import BlockBand.Transmission.Generator.Assembly
public import BlockBand.Transmission.Generator.PowSum

/-!
# The transmission generator theorem with the drift statement discharged

`transmissionGenerator_of_modProd`: `TransmissionGeneratorContract` from the transmission inputs
and the two statements `PowerModulusAlong` and `ProductMartingaleAlong`; `PowerDriftSummable` is
supplied by `powerDriftSummable_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform

/-- **`TransmissionGeneratorContract` from `PowerModulusAlong` and
`ProductMartingaleAlong`.** -/
theorem transmissionGenerator_of_modProd (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hMod : PowerModulusAlong) (hProd : ProductMartingaleAlong) :
    TransmissionGeneratorContract :=
  transmissionGenerator_of hMT hGA hLp (powerDriftSummable_holds hMT hGA hLp hP) hMod hProd

end BlockBand.Transmission.Generator
