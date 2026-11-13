module

public import BlockBand.SourceProcess.ClosedSumProof.Main

/-!
# Closed feasibility and closed tightness from time `s`

* `ClosedFeasible`: eventually in `W`, almost surely on the physical cap event, the closed Gram
  state `closedGramAt` at every grid index `j` with `closeLen s W ≤ j ≤ ⌊WT⌋` is feasible for the
  source signature.
* `ClosedTightS`: the closed Gram coordinates are tight at every time `t₁ ∈ [s, T]`, and their
  continuous parts (after removing `closedJump`) have small oscillation on `[t₁, T]`, uniformly in
  large `W`, on the physical cap event.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLaw

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum

/-- **`ClosedFeasible`** (the projection identity): for every admissible time-`s` frame,
eventually in `W`, almost surely on the physical cap event, the closed Gram state is feasible for
the source signature at every length `closeLen s W ≤ j ≤ ⌊WT⌋`. -/
def ClosedFeasible : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M →
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ᶠ W in atTop, ∀ᵐ y ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw),
      y.1.1 ∈ physCapEvent b E s h K W → ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
        GramFeasible (srcSignature K (Fin p × Fin M)) (closedGramAt b E s T h q W j (Vs W) y)

/-- `ClosedTight` from time `s` on: `s ≤ t₁ ≤ T` (proved as `closedTightS_of`). -/
def ClosedTightS : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M →
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M), ∀ t₁ : ℝ, s ≤ t₁ → t₁ ≤ T →
      (∀ θ : ℝ, 0 < θ → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        ((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)
          {y | y.1.1 ∈ physCapEvent b E s h K W ∧
            C < ‖gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * t₁⌋₊ (Vs W) y)‖} ≤
          ENNReal.ofReal θ) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)
          {y | y.1.1 ∈ physCapEvent b E s h K W ∧ ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T,
            |t - t'| ≤ δ ∧ η < ‖gramEntry e
              (closedGramAt b E s T h q W ⌊(W : ℝ) * t⌋₊ (Vs W) y -
                closedJump b s T q W ⌊(W : ℝ) * t⌋₊ y -
                (closedGramAt b E s T h q W ⌊(W : ℝ) * t'⌋₊ (Vs W) y -
                  closedJump b s T q W ⌊(W : ℝ) * t'⌋₊ y))‖} ≤ ENNReal.ofReal θ)

end BlockBand.SourceProcess.CapLaw
