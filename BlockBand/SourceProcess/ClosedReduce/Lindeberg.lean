module

public import BlockBand.SourceProcess.ClosedSum.Summed

/-!
# A Lindeberg (fourth-moment) clause for the closed coordinates

`ClosedSummed` controls only the conditional first and second moments of the increments of the
closed Gram entries (and the births); `ClosedTight` gives tightness and a modulus **in
probability**. Passing the stopped bracket identity to a weak limit needs uniform integrability
of the square of the stopped compensated coordinate, which contains the exit overshoot
`ΔG` at the trace stop (the full increment is kept at the exit). Neither hypothesis bounds
`E[overshoot² ; overshoot > L]`.

*Why this is a stronger hypothesis.* Add to a process satisfying both hypotheses rare
centred jumps of size `√(log W)` with probability `1/(W log W)` per step. The conditional second
moments still match `W⁻¹ c` (the jumps are part of them), the summed errors do not change, and
the probability of any jump in `[s,T]` is `O(1/log W)`, so tightness and the modulus still hold.
The jumps carry a fixed share of `E Σ|ΔG|²`, which disappears in the weak limit: the limit bracket
is `c` minus that share, so the bracket identity of `IsTestedModel`/`IsBornGramSolution` fails.

The paper supplies exactly this clause in the full-source stopping lemma
(`E Σ_j |ΔZ_j|^p ≤ C_K W^{1-p/2} → 0`, `p > 2`, away from the births), which the closed
path inherits. For the full source it follows from `EarlySummed` for `Φ, …, Φ⁴`
(`fourth_cancel`); `ClosedSummed` has no such powers. `ClosedLindeberg` is that clause for the
closed Gram entries at `p = 4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic
open scoped ENNReal

variable {p K M : ℕ}

/-- The summed fourth moments of the increments of the Gram entry `e` of the closed process, at
steps without a birth, on the cap event and before the trace stop. -/
def closedLindebergErr (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
    ∫⁻ y, (closedAlive (M := M) b E s T h q R W j Vs ∩ noBirth j).indicator
      (fun y => ‖gramEntry e (closedGramAt b E s T h q W (j + 1) Vs y) -
        gramEntry e (closedGramAt b E s T h q W j Vs y)‖ₑ ^ 4) y
      ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)

/-- **The Lindeberg clause of the closed coordinates.** For every admissible time-`s` frame, the
summed fourth moments of the closed Gram increments, on the cap event, before the trace stop and
away from the births, tend to `0`. This is stated as a hypothesis. -/
def ClosedLindeberg : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M → ∀ R : ℝ,
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M),
      Tendsto (fun W => closedLindebergErr b E s T h q R W (Vs W) e) atTop (𝓝 0)

end BlockBand.SourceProcess.ClosedReduce
