module

public import BlockBand.SourceProcess.ContractingWords.IdProjFinal
public import BlockBand.SourceProcess.ContractingWords.Main
public import BlockBand.SourceProcess.CompleteSourceGapBulk.All

/-!
# `WordStepMean`, `WordStepFluct`, and the contracting-words statements from `SummedStep`

The one-step word bounds hold, so the contracting-words statements follow from the summed step
`SummedStep` alone.

* **`wordStepMean_holds`**, **`wordStepFluct_holds`**: the reductions with all four separator
  inputs discharged: `SepMeanIdProj`, `SepFluctIdProj` and
  `SeparatorMeanUniform`, `SeparatorFluctUniform`.
* `contractingWordsEnergyUniform_holds_of_summed`, `contractingWords_holds_of_summed`.

Hypotheses: `MatchedTracesContract`, `GaussianAbsorptionContract`, `ScalarRecursionContract`,
`GaussianLpGradient`, and `SummedStep` for the last two results.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionUniform2

/-- **`WordStepMean`** from the input hypotheses. -/
theorem wordStepMean_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : WordStepMean :=
  wordStepMean_of' hMT hGA hLp hSR (CompleteSourceGapBulk.separatorMeanUniform_holds hGA hLp)
    (CompleteSourceGapBulk.separatorFluctUniform_holds hGA hLp)

/-- **`WordStepFluct`** from the input hypotheses. -/
theorem wordStepFluct_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : WordStepFluct :=
  wordStepFluct_of' hMT hGA hLp hSR (CompleteSourceGapBulk.separatorMeanUniform_holds hGA hLp)
    (CompleteSourceGapBulk.separatorFluctUniform_holds hGA hLp)

/-- **`ContractingWordsEnergyUniformContract`** from the input hypotheses and `SummedStep`. -/
theorem contractingWordsEnergyUniform_holds_of_summed (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hS : SummedStep) : ContractingWordsEnergyUniformContract :=
  contractingWordsEnergyUniform_of hMT hGA hLp hSR (wordStepMean_holds hMT hGA hLp hSR)
    (wordStepFluct_holds hMT hGA hLp hSR) hS

/-- **The `ContractingWordsContract`** from the input hypotheses and `SummedStep`. -/
theorem contractingWords_holds_of_summed (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hS : SummedStep) : ContractingWordsContract :=
  contractingWords_of_uniform (contractingWordsEnergyUniform_holds_of_summed hMT hGA hLp hSR hS)

end BlockBand.SourceProcess.ContractingWords
