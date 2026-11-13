module

public import BlockBand.SourceProcess.ContractingWords.RecursionField
public import BlockBand.SourceProcess.ContractingWords.SummedField

/-!
# The contracting-words lemma: assembly and the fixed-`E` form

`contractingWordsEnergyUniform_of`: the energy-uniform contracting-words statement
`ContractingWordsEnergyUniformContract` follows from the one-step bounds `WordStepMean`,
`WordStepFluct` and the summed step `SummedStep`. `contractingWords_of_uniform` specializes it to
a fixed energy `-2 < E < 2` (`ContractingWordsContract`), using the bulk margin
`min(E + 2, 2 - E)` (`mem_bulk_self`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2

/-- **`ContractingWordsEnergyUniformContract`** from `WordStepMean`, `WordStepFluct` and
`SummedStep`. -/
theorem contractingWordsEnergyUniform_of (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hM : WordStepMean) (hF : WordStepFluct)
    (hS : SummedStep) : ContractingWordsEnergyUniformContract where
  recursion := recursion_of hMT hGA hLp hSR hM hF
  summed := summed_of hS

theorem mem_bulk_self {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **The energy-uniform statement implies the fixed-`E` one** (`ContractingWordsContract`). -/
theorem contractingWords_of_uniform (h : ContractingWordsEnergyUniformContract) :
    ContractingWordsContract where
  recursion := by
    intro b hb0 hb E h1 h2
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    refine ⟨BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb h1 h2,
      fun s hs nT nI q hq d ε T K p hε hεT hp => ?_⟩
    obtain ⟨C, ρ, W₀, hρ0, hρ1, hC⟩ := h.recursion b hb0 hb _ hκ nT nI q hq d ε T K p hε hεT hp
    exact ⟨C, ρ, W₀, hρ0, hρ1, fun W hW => hC W hW E hE s hs⟩
  summed := by
    intro b hb0 hb E h1 h2 nT nI q hq Φ hΦ ε T K hε hεT
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨C, W₀, hC⟩ := h.summed b hb0 hb _ hκ nT nI q hq Φ hΦ ε T K hε hεT
    exact ⟨C, W₀, fun W hW => hC W hW E hE⟩

/-- **`ContractingWordsContract`** from the input hypotheses, `WordStepMean`, `WordStepFluct` and
`SummedStep`. -/
theorem contractingWords_of (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hM : WordStepMean) (hF : WordStepFluct)
    (hS : SummedStep) : ContractingWordsContract :=
  contractingWords_of_uniform (contractingWordsEnergyUniform_of hMT hGA hLp hSR hM hF hS)

end BlockBand.SourceProcess.ContractingWords
