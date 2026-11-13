module

public import BlockBand.Endpoints.Response.NearSchattenLimsup

/-!
# Near-Schatten decay

This file proves `NearSchattenDecayContract` (`nearSchattenDecay_holds`) from the finite fractional
entrance of the near clock (`ClockFractionalEntranceContract`), `FullSourceGeneratorContract`, the
integrated regularized generator inequality at critical limits (`NsRegularizedLimitGenerator`) and
the existence of critical clock limits (`NsCriticalClockLimitsExist`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Endpoints

/-- **Near-Schatten decay**: `NearSchattenDecayContract` from `ClockFractionalEntranceContract`,
`FullSourceGeneratorContract`, `NsRegularizedLimitGenerator` and `NsCriticalClockLimitsExist`
(the latter follows from `FullSourceGeneratorContract` by
`nsCriticalClockLimitsExist_of_contracts`).
-/
theorem nearSchattenDecay_holds (hEnt : ClockFractionalEntranceContract)
    (hGen : FullSourceGeneratorContract) (hRG : NsRegularizedLimitGenerator)
    (hEx : NsCriticalClockLimitsExist) : NearSchattenDecayContract where
  limitDecay := ns_limitDecay hEnt hRG
  limsupDecay := ns_limsupDecay hEnt hRG hGen hEx

end BlockBand.Endpoints
