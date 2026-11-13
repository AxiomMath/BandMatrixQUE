module

public import BlockBand.SourceProcess.ProjSeparator.MeanHolds
public import BlockBand.SourceProcess.ProjSeparator.FluctHolds
public import BlockBand.SourceProcess.ProjSeparator.FarHolds

/-!
# The one-layer estimates: summary

* `projGammaMean_holds hGA hLp hP : ProjGammaMean`;
* `projGammaFluct_holds hGA hLp : ProjGammaFluct` (`p = 2`);
* `injFarTrace_holds hGA : InjFarTrace`;

`slotPins_proved` bundles these three estimates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ContractingWords

/-- The three one-layer estimates `ProjGammaMean`, `ProjGammaFluct` and `InjFarTrace`, from the input
hypotheses. -/
theorem slotPins_proved (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : ProjGammaMean ∧ ProjGammaFluct ∧ InjFarTrace :=
  ⟨projGammaMean_holds hGA hLp hP, projGammaFluct_holds hGA hLp, injFarTrace_holds hGA⟩

end BlockBand.SourceProcess.ProjSeparator
