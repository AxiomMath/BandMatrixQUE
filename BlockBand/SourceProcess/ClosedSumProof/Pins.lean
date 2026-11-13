module

public import BlockBand.SourceProcess.ClosedSum.Main

/-!
# The two auxiliary hypotheses for `ClosedTight`

`closedTight_of` proves `ClosedTight` from `ClosedSummed` and the two statements below. Both are
stated on the objects of `ClosedSummed` (same law `sampledPathLaw ⊗ phaseLaw`, same Gram process
`closedGramAt`, same cap event and trace stop, same steps `n_s ≤ j < ⌊WT⌋`).

* `ClosedFourth`: the summed fourth moments of the closed Gram increments at steps without a birth,
  before the stop, tend to `0`.
* `ClosedStopTail`: for every `θ > 0` some trace level `R` is reached on the cap event with
  probability at most `θ`, for all large `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

variable {W p K M : ℕ}

/-- The summed fourth moments of the steps without birth, before the stop. -/
def closedFourthErr (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
    ∫⁻ y, ‖(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
        gramEntry e (closedGramAt b E s T h q W (j + 1) Vs y) -
          gramEntry e (closedGramAt b E s T h q W j Vs y)) y‖ₑ ^ 4
      ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)

/-- **`ClosedFourth`**: the summed fourth moments `closedFourthErr` tend to `0`. -/
def ClosedFourth : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M → ∀ R : ℝ,
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M),
      Tendsto (fun W => closedFourthErr b E s T h q R W (Vs W) e) atTop (𝓝 0)

/-- The stop event: on the cap event, the trace level `R` is reached at some length
`n_s ≤ i ≤ ⌊WT⌋`. -/
def closedStopEvent (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (SampledPath W p M × ℝ) :=
  {y | y.1.1 ∈ physCapEvent b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * T⌋₊ ∧
    R ≤ ((closedGramAt b E s T h q W i Vs y).1.trace).re}

/-- **`ClosedStopTail`**: for every admissible time-`s` frame and `θ > 0` there is a trace level
`R` whose stop event `closedStopEvent` has probability at most `θ` for all large `W`. -/
def ClosedStopTail : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M →
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ θ : ℝ, 0 < θ → ∃ R : ℝ, ∀ᶠ W in atTop,
      ((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)
        (closedStopEvent (M := M) b E s T h q R W (Vs W)) ≤ ENNReal.ofReal θ

end BlockBand.SourceProcess.ClosedSumProof
