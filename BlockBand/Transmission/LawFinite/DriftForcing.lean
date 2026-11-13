module

public import BlockBand.Transmission.LawFinite.Forcing
public import BlockBand.Transmission.LawFinite.Drift

/-!
# The reciprocal drift from the input hypotheses

**`reciprocalDrift_of_gaussianInputs hGA hLp : ReciprocalDrift`**: the reciprocal drift under
`GaussianAbsorptionContract` and `GaussianLpGradient` (`reciprocalDrift_holds` with
`passiveBounds_holds`).

The forcing, `AbsorbedWardIdentity ∧ InjectionNorms ∧ InjectionMean`, is proved under the same
hypotheses in the sibling module (`forcing_of_gaussianInputs`).
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Transmission.LawFinite

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **`ReciprocalDrift` from the input hypotheses.** -/
theorem reciprocalDrift_of_gaussianInputs (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ReciprocalDrift :=
  reciprocalDrift_holds (PassiveLayer.passiveBounds_holds hGA hLp)

end BlockBand.Transmission.LawFinite
