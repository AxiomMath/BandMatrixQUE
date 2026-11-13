module

public import BlockBand.SourceProcess.ContractingWords.LiftCov
public import BlockBand.SourceProcess.ContractingWords.EarlySummedStep
public import BlockBand.SourceProcess.ContractingWords.EarlySum
public import BlockBand.SourceProcess.ContractingWords.StepHolds

/-!
# The summed step with early births and the contracting-word estimates

The one-step inputs are combined into the summed step with tag births anywhere and into the
uniform contracting-word energy bounds.

* `summedStepAll_of_pins`, `summedStepAll_of_layer`: `SummedStepAll` (births anywhere).
* **`earlySummed_of_layer`**: `FullSourceGenerator.EarlySummed`.
* The forms `OrdinaryDriftStep`, `OrdinaryCovStep` with births after `εW`:
  `ordinaryDriftStep_of_layer`, `ordinaryCovStep_of_layer`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform2
open scoped ENNReal ComplexConjugate

/-- **The field `recursion` of `ContractingWordsEnergyUniformContract`**, from the input
hypotheses only. -/
theorem recursion_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) → ∀ j₀ : ℕ, ε * W ≤ j₀ → (∀ a, k a < j₀) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      let μ := growthPathLaw W b
      let lam : ℂ := thetaStar b E s ^ unconjCount Zs * conj (thetaStar b E s) ^ conjCount Zs
      let Z : ℕ → GrowthPath W → ℂ := fun j ω => productValue b E k q W j ω Zs
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      (∀ j : ℕ, j₀ ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W → ∃ ξ : GrowthPath W → ℂ,
        Integrable ((A j).indicator ξ) μ ∧
        μ[(A j).indicator ξ | growthSigma W j] =ᵐ[μ] 0 ∧
        eLpNorm ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / W) ∧
        eLpNorm ((A j).indicator ξ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / Real.sqrt W)) ∧
      ∀ j : ℕ, j₀ ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm ((A j).indicator (Z j)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * (ρ ^ (j - j₀) + 1 / Real.sqrt W)) :=
  recursion_of hMT hGA hLp hSR (wordStepMean_holds hMT hGA hLp hSR)
    (wordStepFluct_holds hMT hGA hLp hSR)

/-- `SummedStepAll` from the input hypotheses and the two per-word hypotheses
`OrdinaryDriftStepAll`, `OrdinaryCovStepAll` (births anywhere). -/
theorem summedStepAll_of_pins (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hD : OrdinaryDriftStepAll)
    (hCv : OrdinaryCovStepAll) : SummedStepAll :=
  summedStepAll_of hMT hGA hLp hSR hD hCv (ordinaryIncrementAll_holds hMT hGA hLp hSR)

/-- `SummedStepAll` from the input hypotheses and the one-layer hypotheses `LayerDrift`,
`LayerCov`. -/
theorem summedStepAll_of_layer (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hLD : LayerDrift)
    (hLC : LayerCov) : SummedStepAll :=
  summedStepAll_of_pins hMT hGA hLp hSR (ordinaryDriftStepAll_of hMT hGA hLp hSR hLD)
    (ordinaryCovStepAll_of hMT hGA hLp hSR hLC)

/-- **`FullSourceGenerator.EarlySummed`** from the input hypotheses, `LayerDrift` and
`LayerCov`. -/
theorem earlySummed_of_layer (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hLD : LayerDrift)
    (hLC : LayerCov) : FullSourceGenerator.EarlySummed :=
  earlySummed_of (summedStepAll_of_layer hMT hGA hLp hSR hLD hLC)

/-- `OrdinaryDriftStep` from the input hypotheses and `LayerDrift`. -/
theorem ordinaryDriftStep_of_layer (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hLD : LayerDrift) : OrdinaryDriftStep :=
  ordinaryDriftStep_of_all (ordinaryDriftStepAll_of hMT hGA hLp hSR hLD)

/-- `OrdinaryCovStep` from the input hypotheses and `LayerCov`. -/
theorem ordinaryCovStep_of_layer (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hLC : LayerCov) : OrdinaryCovStep :=
  ordinaryCovStep_of_all (ordinaryCovStepAll_of hMT hGA hLp hSR hLC)

/-- **`ContractingWordsEnergyUniformContract`** from the input hypotheses, `LayerDrift` and
`LayerCov` (both proved, as `layerDrift_holds` and `layerCov_holds`). -/
theorem contractingWordsEnergyUniform_of_layer (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hLD : LayerDrift) (hLC : LayerCov) :
    ContractingWordsEnergyUniformContract :=
  contractingWordsEnergyUniform_holds_of_summed hMT hGA hLp hSR
    (summedStep_of_all (summedStepAll_of_layer hMT hGA hLp hSR hLD hLC))

/-- **The `ContractingWordsContract`** from the input hypotheses, `LayerDrift` and `LayerCov`. -/
theorem contractingWords_of_layer (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hLD : LayerDrift) (hLC : LayerCov) :
    ContractingWordsContract :=
  contractingWords_of_uniform (contractingWordsEnergyUniform_of_layer hMT hGA hLp hSR hLD hLC)

end BlockBand.SourceProcess.ContractingWords
