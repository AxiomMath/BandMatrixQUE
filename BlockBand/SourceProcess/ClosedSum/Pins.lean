module

public import BlockBand.SourceProcess.ClosedSum.SelMeas

/-!
# The tightness hypothesis of the closed limit step

`ClosedSummed` controls only the conditional drift and bracket of single Gram entries and the
births. For the open-chain analogue, tightness (`FullSourceGenerator.tightClause_of`) is derived
from `EarlySummed` applied to the powers `Φ, …, Φ⁴` and from `FullSourceStopsContract`; neither is
a consequence of entry-level drift/bracket errors. The closed-path analogue is therefore stated
separately:

**`ClosedTight`** (modelled on the full-source stopping lemma): for every admissible time-`s`
frame, every Gram entry `e` and `s < t₁ < T`, on the physical cap event, the entry of the closed
Gram process at `⌊Wt₁⌋` is tight, and its continuous part `G - J` (births removed,
`closedJump`) has a vanishing modulus on `[t₁, T]`.

`closedValue_eq` records the value identity for the measurable selected frame.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent

variable {W p K M : ℕ}

/-- The births up to length `j` (steps `n_s ≤ i < j`). -/
def closedJump (b s T : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ) (y : SampledPath W p M × ℝ) :
    GramState (SrcCol K (Fin p × Fin M)) :=
  ∑ i ∈ Finset.Ico (closeLen s W) j, birthAt b s T q i y

/-- **Tightness of the closed Gram process**, stated as a hypothesis. -/
def ClosedTight : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M →
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M), ∀ t₁ : ℝ, s < t₁ → t₁ < T →
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

/-- **The value identity with the measurable selected frame**: the capped closed
transform is the capped expectation of the model observable of the closed Gram process at the
final length, with time-`s` frame `physSelFrame`. -/
theorem closedValue_eq (V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ)
    (b E s T h : ℝ) {J : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (a : Fin J → Fin p → ℝ) :
    cappedClosedTransform b E s T h q a K M W =
      ∫ y, (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
          sampledTransformValue a
            (closedGramAt b E s T h q W ⌊(W : ℝ) * T⌋₊ (physSelFrame V b E s h K) y)
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) :=
  cappedClosedTransform_eq_closedGramAt b E s T h hq a W _

end BlockBand.SourceProcess.ClosedSum
