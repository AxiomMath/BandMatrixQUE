module

public import BlockBand.Transmission.LawFinite.InjectionMean
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# The microscopic forcing from the input hypotheses

`forcing_of_gaussianInputs`: from `GaussianAbsorptionContract` and `GaussianLpGradient`, the absorbed Ward
identity, the injection norms and the injection mean hold.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Transmission.LawFinite

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **The microscopic forcing Props from the input hypotheses.** -/
theorem forcing_of_gaussianInputs (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    AbsorbedWardIdentity ∧ InjectionNorms ∧ InjectionMean :=
  ⟨absorbedWardIdentity_holds,
    injectionNorms_holds (PassiveLayer.passiveBounds_holds hGA hLp),
    injectionMean_holds (PassiveLayer.passiveBounds_holds hGA hLp)⟩

end BlockBand.Transmission.LawFinite
