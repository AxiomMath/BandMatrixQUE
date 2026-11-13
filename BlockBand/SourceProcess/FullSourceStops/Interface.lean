module

public import BlockBand.Internal.Contracts.TransmissionUniform2

/-!
# The full-source stops lemma, energy-uniform: the intermediate statements

This file defines `TagSupBulk`, `CurrentNuclearTail` and `CompensatorCoefficientMoments`.

* `TagSupBulk`: the supremum over `j ≤ TW` of one tag mass `W⁻¹Tr Y_{j;k}` has every positive
  moment, uniformly in the birth index `k` and on `bulkInterval κ`. It is proved (`tagSupBulk_of`)
  from the stopped weighted tag recursion (one stopped step against every past event,
  `stopped_tag_step_on`), an elementary maximal inequality for weighted supermartingales (`ville`),
  a dyadic tail-to-moment bound, and Hölder plus the superexponential scalar exit off the stop.

These statements give the fields of `FullSourceStopsContract`:
* `supMoments`: tags directly; an interval source is `Tr Q = Σ_i q_i W⁻¹ t_{j;i}`, so its supremum
  is at most `‖q‖_∞ W⁻¹ Σ_i sup_j t_{j;i}`, and the power-mean inequality reduces it to
  `TagSupBulk`.
* `tail`: Markov's inequality from `supMoments` for the sources, plus the current tail bound
  `CurrentNuclearTail`.
* `compensatorUI`: the time-integral argument (Cauchy–Schwarz over the at most `TW` steps, then
  `E[X; X > M] ≤ E X²/M`) from the coefficient bound `CompensatorCoefficientMoments` (every
  coefficient is a fixed polynomial in `g` and the source traces).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **Supremum moments of one tag.** `b, κ, T, p > 0`, then `C, W₀`. For `W ≥ W₀`,
every `E ∈ bulkInterval κ` and every birth index `k`:
`E[(sup_{j ≤ TW} W⁻¹Re Tr Y_{j;k})^p] ≤ C` (the tag is zero for `j ≤ k`). -/
def TagSupBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 0 < p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ k : ℕ,
      ∫⁻ ω, (⨆ (j : ℕ) (_ : (j : ℝ) ≤ T * W),
          ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W j k ω).trace.re)) ^ p
        ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- **The tail of the current**: `limsup_W sup_{E ∈ bulkInterval κI} P(∃ j ∈ [εW, TW],
Tr|J_j| > K) ≤ C/K` for every `K > 0`. -/
def CurrentNuclearTail : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ C : ℝ, ∀ K : ℝ, 0 < K →
      limsup (fun W : ℕ => ⨆ (E : ℝ) (_ : E ∈ bulkInterval κI),
          growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
            K < nuclearNorm (pathCurrent b E W j ω)}) atTop ≤ ENNReal.ofReal (C / K)

/-- **Second moments of the compensator coefficients.** `b, κI`, the source family, an ordinary trace
polynomial `Φ` and `0 < ε < T`, then `C, W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κI`, every tag
birth vector `k` and every step `εW ≤ j ≤ TW`, the drift coefficient `𝒜_{(j+1)/W}Φ(Z_j)` and the
bracket coefficient `Γ(Φ)(Z_j)` are measurable and have second moments at most `C`. (Measurability
holds because every word value is the trace of a product of measurable path matrices.) Every word is
bounded without `Tr|J|` (a word with a source letter by a product of source traces, a word in `J, P`
only by `2g`, using `‖J‖ ≤ 1`, `Tr J = 0`, `Tr JP = -g`, `Tr J² = 2g`), so each coefficient is at
most a fixed polynomial in `g` and the source traces, and Hölder with the conductance moments and
the (fixed-`j`) source moments concludes. -/
def CompensatorCoefficientMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ k : Fin nT → ℕ,
      ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W →
        Measurable (fun ω => polyValue b E k q W j ω
            (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ∧
          Measurable (fun ω => polyValue b E k q W j ω (wordCarre b E Φ)) ∧
          ∫⁻ ω, ‖polyValue b E k q W j ω (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)‖ₑ ^ 2
            ∂growthPathLaw W b ≤ ENNReal.ofReal C ∧
          ∫⁻ ω, ‖polyValue b E k q W j ω (wordCarre b E Φ)‖ₑ ^ 2 ∂growthPathLaw W b ≤
            ENNReal.ofReal C

end BlockBand.SourceProcess.FullSourceStops
