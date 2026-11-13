module

public import BlockBand.Transmission.Generator.AssemblyDrift
public import BlockBand.Transmission.Generator.ModAlong
public import BlockBand.Transmission.Generator.ModProd

/-!
# The transmission generator theorem with the drift and modulus statements discharged

**`transmissionGenerator_of_prod hMT hGA hLp hP hProd`**: `transmissionGenerator_of_modProd`
with `PowerModulusAlong` supplied by `powerModulusAlong_holds hMT hGA hLp hP`. The only remaining
hypothesis is `ProductMartingaleAlong` (the product half of `martingale`, along a moving
energy).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform

/-- **`TransmissionGeneratorContract` from `ProductMartingaleAlong`.** -/
theorem transmissionGenerator_of_prod (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hProd : ProductMartingaleAlong) : TransmissionGeneratorContract :=
  transmissionGenerator_of_modProd hMT hGA hLp hP (powerModulusAlong_holds hMT hGA hLp hP) hProd

end BlockBand.Transmission.Generator
