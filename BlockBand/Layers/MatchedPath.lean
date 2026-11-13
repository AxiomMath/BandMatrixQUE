module

public import BlockBand.Layers.CoreTraces
public import BlockBand.Layers.PathTraces

/-!
# The path clause of the matched-traces theorem and the stopped scalar recursion

The core bound `CoreTraceBound` (the `path` clause restricted to the cores `r ∈ {1, 2}`) is
supplied by `coreTraces_holds` (Steps 1–2 of the proof of the matched-traces theorem). This gives
constructors, from `ConditionalBlockGUECount` and `GaussianLpGradient`, for
* the `path` field of `MatchedTracesContract` (`matchedTracesPath_holds`; the matched-trace
  moments, Steps 3–4): every `1 ≤ r ≤ TW`, both parities, law `pathLaw W r b`, deterministic
  `E ∈ I`;
* the structure `ScalarRecursionContract` (`scalarRecursionContract_holds`; the one-step
  matched-trace recursion and the scalar exit bound).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts MeasureTheory

/-- **The `path` clause of the matched-traces theorem** (the matched-trace moments), from
`ConditionalBlockGUECount` and `GaussianLpGradient`: `matchedTracesPath_of_core` with the cores
supplied by `coreTraces_holds`. -/
theorem matchedTracesPath_holds (hcount : Inputs.ConditionalBlockGUECount)
    (hgrad : Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ Layers.bulkInterval κ,
          eLpNorm (fun ω => max ‖Layers.blockTrace (Layers.pathPortResolvent b E ω) 0 -
                Layers.matchedA E‖
              ‖Layers.blockTrace (Layers.pathPortResolvent b E ω) 1 - Layers.matchedA E‖)
            (ENNReal.ofReal p) (Layers.pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) :=
  matchedTracesPath_of_core hcount hgrad (coreTraces_holds hcount hgrad)

/-- **`ScalarRecursionContract`** (the one-step matched-trace recursion and the scalar exit bound,
displays in the proof of the matched-traces theorem), from `ConditionalBlockGUECount` and
`GaussianLpGradient`. -/
theorem scalarRecursionContract_holds (hcount : Inputs.ConditionalBlockGUECount)
    (hgrad : Inputs.GaussianLpGradient) : Layers.ScalarRecursionContract :=
  scalarRecursion_holds hcount hgrad (coreTraces_holds hcount hgrad)

end BlockBand.Layers
