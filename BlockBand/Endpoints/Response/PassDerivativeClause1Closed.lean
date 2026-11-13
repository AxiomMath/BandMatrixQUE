module

public import BlockBand.Endpoints.Response.PathFractionalInverse
public import BlockBand.Endpoints.Sine.GUELawBridge

/-!
# The pass-derivative lemma, clause 1, from the GUE count

This file proves `PathFractionalInverse` from `ConditionalBlockGUECount`
(`pathFractionalInverse_of_contracts`, via `pathFractionalInverse_holds` and `guelawBridge_holds`) and
hence clause 1 of the pass-derivative lemma from `FullSourceMomentsContract` and
`ConditionalBlockGUECount` alone (`passDerivative_clause1_of_contracts`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionStatements

/-- `PathFractionalInverse` from the conditional block-GUE count `ConditionalBlockGUECount`
alone. -/
theorem pathFractionalInverse_of_contracts (hCount : ConditionalBlockGUECount) :
    PathFractionalInverse :=
  pathFractionalInverse_holds hCount guelawBridge_holds

/-- **The pass-derivative lemma, clause 1**: for every fixed bounded
nonnegative `q` and `0 < s < 1`, the expected right difference quotients of `F_L + F_R` on the
unabsorbed path (`growthPathLaw W b`, `0 < b < 1/2`, bulk `E`, lengths `j W / W → τ > 0`,
`x ≥ 0`, `0 ≤ y < 1`) differ from the expected zero-source derivative by `C (κ^{s/2} + κ)` for
all `W ≥ W₀` and all `κ > 0`.
Hypotheses: only `FullSourceMomentsContract` and `ConditionalBlockGUECount`.
-/
theorem passDerivative_clause1_of_contracts (hMom : FullSourceMomentsContract)
    (hCount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ τ : ℝ, 0 < τ → ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 →
    ∀ q : ℝ → ℝ, (∀ t, 0 ≤ q t) → BddAbove (Set.range q) →
    ∀ s : ℝ, 0 < s → s < 1 →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ κ : ℝ, 0 < κ →
      |(∫ ω, (portRatioSum b E x y W (j W) q κ ω - portRatioSum b E x y W (j W) q 0 ω) / κ
          ∂growthPathLaw W b) -
        ∫ ω, derivWithin (fun κ' => portRatioSum b E x y W (j W) q κ' ω) (Set.Ici 0) 0
          ∂growthPathLaw W b| ≤ C * (κ ^ (s / 2) + κ) :=
  passDerivative_clause1 hMom (pathFractionalInverse_of_contracts hCount)

end BlockBand.Endpoints
