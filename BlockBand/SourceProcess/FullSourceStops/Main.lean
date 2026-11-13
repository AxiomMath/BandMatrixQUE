module

public import BlockBand.SourceProcess.FullSourceStops.Tail
public import BlockBand.SourceProcess.FullSourceStops.Compensator

/-!
# The full-source stops lemma: assembly

`fullSourceStopsEnergyUniform_of`: the tag supremum moments, the current tail bound and the
compensator coefficient moments give the energy-uniform full-source stops statement;
`fullSourceStops_of_uniform` specializes it to a fixed energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2
open scoped ENNReal

/-- **`FullSourceStopsEnergyUniformContract`** from the input hypotheses, `CurrentNuclearTail`
and `CompensatorCoefficientMoments`. -/
theorem fullSourceStopsEnergyUniform_of (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hJ : CurrentNuclearTail)
    (hCC : CompensatorCoefficientMoments) : FullSourceStopsEnergyUniformContract where
  tail := tail_of (tagSupBulk_holds hGA hLp hSR) hJ
  supMoments := supMoments_of (tagSupBulk_holds hGA hLp hSR)
  compensatorUI := compensatorUI_of hCC

theorem mem_bulk_self {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **The fixed-`E` statement `FullSourceStopsContract`** from the energy-uniform one. -/
theorem fullSourceStops_of_uniform (h : FullSourceStopsEnergyUniformContract) :
    FullSourceStopsContract where
  tail := by
    intro b hb0 hb E h1 h2 nT nI q hq ε T hε hεT
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨C, hC⟩ := h.tail b hb0 hb _ hκ nT nI q hq ε T hε hεT
    refine ⟨C, fun K hK => le_trans (limsup_le_limsup (Eventually.of_forall fun W => ?_))
      (hC K hK)⟩
    exact le_iSup₂_of_le (f := fun (E' : ℝ) (_ : E' ∈ bulkInterval (min (E + 2) (2 - E))) =>
      ⨆ k : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
        K < traceLoad b E' k q W j ω}) E hE le_rfl
  supMoments := by
    intro b hb0 hb E h1 h2 nT nI q hq ε T p hε hεT hp
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨C, W₀, hC⟩ := h.supMoments b hb0 hb _ hκ nT nI q hq ε T p hε hεT hp
    exact ⟨C, W₀, fun W hW => hC W hW E hE⟩
  compensatorUI := by
    intro b hb0 hb E h1 h2 nT nI q hq Φ hΦ ε T η hε hεT hη
    obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
    obtain ⟨M, W₀, hM⟩ := h.compensatorUI b hb0 hb _ hκ nT nI q hq Φ hΦ ε T η hε hεT hη
    exact ⟨M, W₀, fun W hW => hM W hW E hE⟩

/-- **`FullSourceStopsContract`** from the input hypotheses, `CurrentNuclearTail` and
`CompensatorCoefficientMoments`. -/
theorem fullSourceStops_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hJ : CurrentNuclearTail)
    (hCC : CompensatorCoefficientMoments) : FullSourceStopsContract :=
  fullSourceStops_of_uniform (fullSourceStopsEnergyUniform_of hGA hLp hSR hJ hCC)

end BlockBand.SourceProcess.FullSourceStops
