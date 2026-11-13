module

public import BlockBand.SourceProcess.ContractingWords.SlotPinsHolds
public import BlockBand.SourceProcess.ProjSeparator.AllPins

/-!
# The contracting-words statements

The one-layer drift and covariance bounds hold, and therefore so do the contracting-words
statements, the summed step with early births and the full-source generator statement.

* `layerDrift_holds`, `layerCov_holds`: `LayerDrift`, `LayerCov`;
* `contractingWordsEnergyUniform_holds : ContractingWordsEnergyUniformContract`;
* `contractingWords_holds : ContractingWordsContract`;
* `earlySummed_holds : FullSourceGenerator.EarlySummed`;
* `fullSourceGenerator_holds : FullSourceGeneratorContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform2

/-- **`LayerDrift`** from the input hypotheses. -/
theorem layerDrift_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : LayerDrift :=
  have h := BlockBand.SourceProcess.ProjSeparator.slotPins_all hGA hLp hP
  layerDrift_of hGA hLp hP h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **`LayerCov`** from the input hypotheses. -/
theorem layerCov_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : LayerCov :=
  layerCov_of hGA hLp hP (BlockBand.SourceProcess.ProjSeparator.projGammaFluct_holds hGA hLp)

/-- **The `ContractingWordsEnergyUniformContract`** from the input hypotheses. -/
theorem contractingWordsEnergyUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) : ContractingWordsEnergyUniformContract :=
  contractingWordsEnergyUniform_of_layer hMT hGA hLp hSR (layerDrift_holds hGA hLp hP)
    (layerCov_holds hGA hLp hP)

/-- **The `ContractingWordsContract`** from the input hypotheses. -/
theorem contractingWords_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) : ContractingWordsContract :=
  contractingWords_of_layer hMT hGA hLp hSR (layerDrift_holds hGA hLp hP)
    (layerCov_holds hGA hLp hP)

/-- **`FullSourceGenerator.EarlySummed`** from the input hypotheses. -/
theorem earlySummed_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) : FullSourceGenerator.EarlySummed :=
  earlySummed_of_layer hMT hGA hLp hSR (layerDrift_holds hGA hLp hP) (layerCov_holds hGA hLp hP)

/-- **The `FullSourceGeneratorContract`** from the input hypotheses. -/
theorem fullSourceGenerator_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hP : GaussianPoincare) : FullSourceGeneratorContract :=
  FullSourceGenerator.fullSourceGenerator_holds_of_early (earlySummed_holds hMT hGA hLp hSR hP)
    (BlockBand.Transmission.FractionalBulk.fullSourceStops_holds hMT hGA hLp hSR hP)
    hMT hGA hLp hSR

end BlockBand.SourceProcess.ContractingWords
