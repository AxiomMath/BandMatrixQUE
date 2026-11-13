module

public import BlockBand.SourceProcess.ProjSeparator.Main
public import BlockBand.SourceProcess.ProjSeparator.InjNearHolds

/-!
# The four one-layer estimates

`slotPins_all`: under `GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`,
the four one-layer estimates hold: the mean `ProjGammaMean` and the fluctuation `ProjGammaFluct`
of the projected separator, the near injected trace `InjNearMeanW2` (with its `W⁻²` term) and
the far injected trace `InjFarTrace`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ContractingWords

/-- **All four one-layer estimates** (`InjNearMean` replaced by `InjNearMeanW2`), from the input
hypotheses. -/
theorem slotPins_all (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : ProjGammaMean ∧ ProjGammaFluct ∧ InjNearMeanW2 ∧ InjFarTrace :=
  ⟨projGammaMean_holds hGA hLp hP, projGammaFluct_holds hGA hLp, injNearMeanW2_holds hGA hLp,
    injFarTrace_holds hGA⟩

end BlockBand.SourceProcess.ProjSeparator
