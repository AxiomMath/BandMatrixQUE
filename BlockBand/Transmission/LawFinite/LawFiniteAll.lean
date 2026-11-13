module

public import BlockBand.Transmission.LawFinite.All
public import BlockBand.Transmission.LawFinite.DriftForcing
public import BlockBand.Transmission.LawFinite.EntranceBulk
public import BlockBand.Transmission.Assembly.PassiveInitialScalar

/-!
# The finite-`W` entrance from the input hypotheses

The finite-`W` statements of the transmission law hold under `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient`.

* `finiteCoreEntrance_of_baseContracts`, `transmissionEntranceBulk_of_baseContracts`,
  `transmissionEntranceAlong_of_baseContracts`: the finite core and the entrance bound;

The reciprocal drift and the forcing under the Gaussian hypotheses,
`reciprocalDrift_of_gaussianInputs` and `forcing_of_gaussianInputs`, and the Ginibre
small-singular-value fraction, `ginibreSmallSingularFraction_holds`, are proved in sibling modules.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Transmission.LawFinite

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`FiniteCoreEntrance` from the input hypotheses.** -/
theorem finiteCoreEntrance_of_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : FiniteCoreEntrance :=
  finiteCoreEntrance_of (PassiveLayer.passiveBounds_holds hGA hLp)
    (Assembly.passiveInitialScalar_holds hMT hGA hLp)

/-- **`TransmissionEntranceBulk` from the input hypotheses.** -/
theorem transmissionEntranceBulk_of_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : TransmissionEntranceBulk :=
  transmissionEntranceBulk_of (PassiveLayer.passiveBounds_holds hGA hLp)
    (Assembly.passiveInitialScalar_holds hMT hGA hLp)

/-- **`TransmissionEntranceAlong` from the input hypotheses** (via `entranceAlong_of_bulk`). -/
theorem transmissionEntranceAlong_of_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : TransmissionEntranceAlong :=
  entranceAlong_of_bulk (transmissionEntranceBulk_of_baseContracts hMT hGA hLp)

end BlockBand.Transmission.LawFinite
