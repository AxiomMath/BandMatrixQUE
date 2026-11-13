module

public import BlockBand.SourceProcess.ContractingWords.LayerCovProof
public import BlockBand.SourceProcess.ContractingWords.EarlyHolds
public import BlockBand.SourceProcess.FullSourceGenerator.LimGenerator
public import BlockBand.Transmission.FractionalBulk.Main

/-!
# The contracting-words statements from the one-layer slot bounds

The one-layer drift and covariance bounds give the contracting-words statements, the summed step
with early births and the full-source generator statement, under the Gaussian and projection
hypotheses on the fresh layer.

* `layerDrift_of`, `layerCov_of`: `LayerDrift`, `LayerCov`;
* `contractingWordsEnergyUniform_of_slotPins`, `contractingWords_of_slotPins`;
* `earlySummed_of_slotPins : FullSourceGenerator.EarlySummed`;
* `fullSourceGenerator_of_slotPins : FullSourceGeneratorContract` (via
  `fullSourceGenerator_holds_of_early`, `hFS := FractionalBulk.fullSourceStops_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform2

/-- **`LayerDrift`** from the input hypotheses and the four one-layer slot hypotheses. -/
theorem layerDrift_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    LayerDrift :=
  layerDrift_of_pins hGA hLp hP hΓm hΓf hIn hIf

/-- **`LayerCov`** from the input hypotheses and `ProjGammaFluct`. -/
theorem layerCov_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓf : ProjGammaFluct) : LayerCov :=
  layerCov_of_pins hGA hLp hP hΓf

/-- **The `ContractingWordsEnergyUniformContract`** from the slot hypotheses. -/
theorem contractingWordsEnergyUniform_of_slotPins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    ContractingWordsEnergyUniformContract :=
  contractingWordsEnergyUniform_of_layer hMT hGA hLp hSR
    (layerDrift_of hGA hLp hP hΓm hΓf hIn hIf) (layerCov_of hGA hLp hP hΓf)

/-- **The `ContractingWordsContract`** from the slot hypotheses. -/
theorem contractingWords_of_slotPins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    ContractingWordsContract :=
  contractingWords_of_layer hMT hGA hLp hSR
    (layerDrift_of hGA hLp hP hΓm hΓf hIn hIf) (layerCov_of hGA hLp hP hΓf)

/-- **`FullSourceGenerator.EarlySummed`** from the one-layer slot bounds. -/
theorem earlySummed_of_slotPins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    FullSourceGenerator.EarlySummed :=
  earlySummed_of_layer hMT hGA hLp hSR
    (layerDrift_of hGA hLp hP hΓm hΓf hIn hIf) (layerCov_of hGA hLp hP hΓf)

/-- **The `FullSourceGeneratorContract`** from the slot hypotheses. -/
theorem fullSourceGenerator_of_slotPins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    FullSourceGeneratorContract :=
  FullSourceGenerator.fullSourceGenerator_holds_of_early
    (earlySummed_of_slotPins hMT hGA hLp hSR hP hΓm hΓf hIn hIf)
    (BlockBand.Transmission.FractionalBulk.fullSourceStops_holds hMT hGA hLp hSR hP)
    hMT hGA hLp hSR

end BlockBand.SourceProcess.ContractingWords
