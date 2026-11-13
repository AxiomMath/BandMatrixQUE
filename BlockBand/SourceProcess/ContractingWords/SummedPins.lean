module

public import BlockBand.SourceProcess.ContractingWords.Interface

/-!
# `SummedStep` word by word: the per-word inputs

`SummedStep` concerns a whole ordinary trace polynomial `Φ`. Its proof
(`summedStep_of`) is the product rule: the exact second-order Taylor expansion
`ΔΦ = Σ_w ∂_wΦ Δ_w + ½Σ_{w,v} ∂_v∂_wΦ Δ_wΔ_v + R`, `|R| ≤ C L^N (Σ_w|Δ_w|)³`
(`taylor_bound`), the pull-out of the old coefficients `∂_wΦ(Z_j)`, Cauchy–Schwarz and the load
moments. What remains are three statements about **single ordinary words** `w, v` (letters
`J, Q_a`, separators `I, P`), at the same data and window as `SummedStep`, uniform in words of
length `≤ d`, with `Δ_w = Tr w(j+1) - Tr w(j)`, `A = {j < σ_K}`, `F_j = growthSigma W j`,
`t = (j+1)/W`, `r_j = restartIndex ε W k j`:
* `OrdinaryDriftStep` (first conditional increment of one word):
  `‖1_A(E_j[1_AΔ_w] - W⁻¹(drift_w + inj_w(t))(Z_j))‖_{L²} ≤ CW⁻¹(ρ^{j-r_j} + W^{-1/2})`.
  Content: separators `I ↦ NN* = I + 𝓔`, `P ↦ P + P𝓔P - (D₀g/2W)P + 𝓩 + 𝓡`,
  the exact Ward mean `E_j𝓔 = -(2iη)⁻¹ΩP𝕊 + h.c. + O(δ₀² + W⁻²)` paired with old letters (a
  contracting word, decaying like `ρ^{j-r_j}` by `recursion`), the second-order pairs
  (`pairTerm`, from the full-source covariance lemma), the injection `d_*q_a(t)` and
  the `≥ 3` centered factors (`W^{-3/2}`).
* `OrdinaryCovStep` (second conditional increment of a pair of words):
  `‖1_A(E_j[1_AΔ_wΔ_v] - W⁻¹cov_{w,v}(Z_j))‖_{L²} ≤ CW⁻¹(ρ^{j-r_j} + W^{-1/2})`
  (`crossTerm`, the same-sign covariance tensors giving contracting words).
* `OrdinaryIncrement`: `‖1_AΔ_w‖_{L^p} ≤ C W^{-1/2}` for every `p ≥ 1`.
Measure `growthPathLaw W b`; constants depend on `b, κI`, the sources, `d, ε, T, K` (and `p`),
uniform in `W ≥ W₀`, `E ∈ bulkInterval κI`, tag births `k_a ≥ εW`, steps `εW ≤ j`, `j ≠ k_a`,
`j + 1 ≤ TW`, words.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- The increment `Δ_w = Tr w(j+1) - Tr w(j)` of one word. -/
def wordInc (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (w : TraceWord nT nI) (ω : GrowthPath W) : ℂ :=
  wordValue b E k q W (j + 1) ω w - wordValue b E k q W j ω w

/-- The step time `t = (j+1)/W`. -/
abbrev stepTime (W j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) / W

/-- The per-step error profile `CW⁻¹(ρ^{j-r_j} + W^{-1/2})` of `SummedStep`. -/
def stepErr (C ρ ε : ℝ) (W : ℕ) {nT : ℕ} (k : Fin nT → ℕ) (j : ℕ) : ℝ :=
  C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)

/-- **The first conditional increment of one ordinary word.** -/
def OrdinaryDriftStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K : ℝ), 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[(alive b E k q K ε W j).indicator (wordInc b E k q W j w) |
              growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
              MvPolynomial.C (wordInjection b q (stepTime W j) w)))
          2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C ρ ε W k j)

/-- **The second conditional increment of a pair of ordinary words.** -/
def OrdinaryCovStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K : ℝ), 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w v : TraceWord nT nI, IsOrdinaryWord w → IsOrdinaryWord v → w.length ≤ d →
        v.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[(alive b E k q K ε W j).indicator
              (fun ω => wordInc b E k q W j w ω * wordInc b E k q W j v ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) w v))
          2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C ρ ε W k j)

/-- **The size of one increment** (proved in `ordinaryIncrement_holds`). -/
def OrdinaryIncrement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (C / Real.sqrt W)

end BlockBand.SourceProcess.ContractingWords
