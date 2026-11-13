module

public import BlockBand.SourceProcess.BornRestart.StageTwoBr

/-!
# `BornUnique.BornRestart` holds

A born Gram solution restarted at a `𝓖₀`-measurable time `α(β)` is again a born Gram solution,
for the restarted filtration and with births `β - α(β)` (`bornRestart_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c} {α : (F → ℝ) → ℝ≥0} {Ω : Type} {m : MeasurableSpace Ω}
  {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω} [IsProbabilityMeasure Q] {β : Ω → F → ℝ}
  {G : ℝ≥0 → Ω → GramState c}

/-- **The restarted process is a born Gram solution** for the restarted filtration, with
births `β - α(β)`. -/
theorem isBornGramSolution_rsH (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) :
    IsBornGramSolution Q (rsFil hα hβ) D0 D
      (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) (rsH α β G) where
  adapted := stronglyMeasurable_rsH hα hβ hG.adapted
  jump u := stronglyMeasurable_rsJump hα hβ u
  continuous := by
    filter_upwards [hG.continuous] with ω hc
    exact continuous_rsH hc
  feasible := by
    filter_upwards [hG.continuous, hG.feasible] with ω hc hf t
    rw [rsH_eq hc]
    exact hf _
  drift K e := rs_drift_clause hα hβ hG K e
  bracket K e e' := rs_bracket_clause hα hβ hG K e e'

/-- **`BornRestart` holds** (no hypotheses). -/
theorem bornRestart_holds : BornRestart := by
  intro c F _ _ _ D0 D j α hα Ω m 𝓖 Q β G hQ hβ hG
  exact ⟨rsFil hα hβ, rsH α β G, measurable_beta_rsFil hα hβ, isBornGramSolution_rsH hα hβ hG,
    by
      filter_upwards [hG.continuous] with ω hc u
      exact rsH_eq hc u⟩

end BlockBand.SourceProcess.BornRestart
