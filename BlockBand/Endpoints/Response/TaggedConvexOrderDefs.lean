module

public import BlockBand.Endpoints.Sine.LocalMassFlatDefs
public import BlockBand.Internal.Contracts.TransmissionUniform
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Convex.Basic

/-!
# Definitions for the convex polynomial comparison of the tagged response

Geometric Brownian comparison: `tco_gbmExpect D₀ d t φ = E φ(d e^{√D₀ B_t - D₀t/2})`,
`B_t ~ N(0,t)` (`gaussianReal 0 t`), written as a Gaussian integral (no process is needed: for
polynomial `φ` it is an explicit finite sum of exponentials).

## Statements

* `TaggedConvexOrderStatement`: the tagged convex order theorem in the energy-uniform reading
  (every tagged sequence with moving energies `e_j → E`): for every limiting law `ν` of
  `Z_{n_j;k_j}` along a subsequence, every convex polynomial `φ` on `[0,∞)` is `ν`-integrable with
  `∫φ dν ≤ E φ(d e^{√D₀B_{τ-s} - D₀(τ-s)/2})`; `∫ x dν = d`; every fixed moment converges along the
  subsequence; and the averaged clause `LmfTaggedFlat` (the tagged flat bound and the `M_W`
  clause, energy-uniform, in the form used by the local mass flatness theorem).
* `TaggedConvexOrderFixedStatement`: the same at a fixed energy `E` (constant energies), with the
  fixed-energy averaged clause `TaggedFlatFixedEnergy`.
* `TcoTagComparisonCore`: the prelimit comparison, i.e. the one-step tagged convex generator
  expansion through the full-source covariance lemma, the summed remainder through the
  contracting-words and full-source-stops lemmas, the backward comparison with the geometric
  Brownian polynomial, and the initial value at the injection. Along every tagged sequence and
  for every convex polynomial `φ`, `limsup_j E φ(Z_{n_j;k_j}) ≤ E φ(d e^{√D₀B_{τ-s} - D₀(τ-s)/2})`.
  `TcoTagComparisonCoreFixed` is the same at constant energy `E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The geometric Brownian expectation `E φ(d e^{√D₀ B_t - D₀t/2})`, `B_t ~ N(0, t)`
(`gaussianReal 0 t`; for `t < 0` the variance is `0`): the right side of the convex polynomial
comparison at `t = τ - s`, and the backward polynomial `u(t,x)` at `x = d`. -/
def tco_gbmExpect (D0 d t : ℝ) (φ : ℝ[X]) : ℝ :=
  ∫ x, φ.eval (d * Real.exp (Real.sqrt D0 * x - D0 * t / 2)) ∂gaussianReal 0 t.toNNReal

/-- A tagged sequence (`k/W → s`, `n/W → τ ≥ s`): widths `W_j → ∞`, path lengths `n_j`, birth
indices `k_j < n_j` (block `k_j + 1 ≤ n_j`), with `k_j/W_j → s` and `n_j/W_j → τ`, and energies
`e_j → E` at which the path is evaluated (the energy-uniform reading; `τ ≥ s` follows from
`k_j < n_j`). -/
structure TcoTagSequence (s τ E : ℝ) where
  W : ℕ → ℕ
  n : ℕ → ℕ
  k : ℕ → ℕ
  energy : ℕ → ℝ
  W_pos : ∀ j, 0 < W j
  width_tendsto : Tendsto W atTop atTop
  tag_lt : ∀ j, k j < n j
  tag_tendsto : Tendsto (fun j => (k j : ℝ) / (W j : ℝ)) atTop (𝓝 s)
  ratio_tendsto : Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 τ)
  energy_tendsto : Tendsto energy atTop (𝓝 E)

/-- `Z_{n_j;k_j} = W_j⁻¹ h*Y_{n_j;k_j}h` along a tagged sequence, at energy `e_j`. -/
def tco_tagZ (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) (j : ℕ) :
    GrowthPath (σ.W j) × (Fin 2 × Fin (σ.W j) → ℂ) → ℝ :=
  lmf_tagResponseClock b (σ.energy j) (σ.W j) (σ.n j) (σ.k j)

/-- Prelimit convex comparison along one tagged sequence: for every polynomial `φ` convex on
`[0,∞)` and every `δ > 0`, eventually `E φ(Z_{n_j;k_j}) ≤ E φ(d e^{√D₀B_{τ-s}-D₀(τ-s)/2}) + δ`
(`D₀ = D₀(E)` at the base energy, `d = d_*`). -/
def TcoConvexComparisonAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ φ : ℝ[X], ConvexOn ℝ (Set.Ici 0) (fun x => φ.eval x) → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ j in atTop, ∫ x, φ.eval (tco_tagZ b σ j x) ∂probedClockLaw (σ.W j) b ≤
      tco_gbmExpect (transportD0 b E) (dStar b) (τ - s) φ + δ

/-- **The prelimit tagged convex comparison, energy-uniform.**
Fixed `0 < b < 1/2`, a bulk energy `-2 < E < 2`, `s > 0`; for every tagged sequence
(`W_j → ∞`, `k_j < n_j`, `k_j/W_j → s`, `n_j/W_j → τ`, energies `e_j → E`) the convex comparison
`TcoConvexComparisonAlong` holds. The paper proves this at fixed `E` from the full-source
covariance lemma, the contracting-words and full-source-stops lemmas, the full tag-clock moments
and the injection ladder. `FullSourceMomentsEnergyUniformContract` holds along moving energies,
but `FullSourceCovarianceContract`, `ContractingWordsContract`, `FullSourceStopsContract` and
`TagBirthValueContract` hold only at a fixed bulk energy with constants depending on it; the
moving-energy reading needs them uniformly along `e_j → E`. It is proved from the
energy-uniform contracts by `tcoTagComparisonCore_of_uniformContracts`.
-/
def TcoTagComparisonCore : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, TcoConvexComparisonAlong b σ

/-- **The prelimit tagged convex comparison at fixed energy**: `TcoTagComparisonCore`
restricted to tagged sequences at the constant energy `E`.
-/
def TcoTagComparisonCoreFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcoConvexComparisonAlong b σ

/-- The limiting-law clauses of the tagged convex order theorem along one tagged sequence. For
every subsequence `ψ` along which the laws of `Z_{n_j;k_j}` converge weakly to a probability
measure `ν` (bounded continuous tests): every polynomial `φ` convex on `[0,∞)` is `ν`-integrable
with `∫ φ dν ≤ E φ(d e^{√D₀B_{τ-s}-D₀(τ-s)/2})`; the mean is `∫ x dν = d`; and every fixed
moment converges, `E Z_{ψ i}^m → ∫ x^m dν`. -/
def TcoLimitLawClauses (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (ψ : ℕ → ℕ) (ν : Measure ℝ), StrictMono ψ → IsProbabilityMeasure ν →
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun i => ∫ x, f (tco_tagZ b σ (ψ i) x)
        ∂probedClockLaw (σ.W (ψ i)) b) atTop (𝓝 (∫ x, f x ∂ν))) →
    (∀ φ : ℝ[X], ConvexOn ℝ (Set.Ici 0) (fun x => φ.eval x) →
        Integrable (fun x => φ.eval x) ν ∧
        ∫ x, φ.eval x ∂ν ≤ tco_gbmExpect (transportD0 b E) (dStar b) (τ - s) φ) ∧
      ∫ x, x ∂ν = dStar b ∧
      ∀ m : ℕ, Integrable (fun x => x ^ m) ν ∧ Tendsto (fun i => ∫ x, (tco_tagZ b σ (ψ i) x) ^ m
        ∂probedClockLaw (σ.W (ψ i)) b) atTop (𝓝 (∫ x, x ^ m ∂ν))

/-- The averaged clause at the fixed energy `E` (the tagged flat bound and the `M_W` clause):
`LmfTaggedFlat` restricted to clock sequences with constant energy `E`. Quantifiers: `b`, bulk
`E`, `T₀`, `p ≥ 1`; then `C = C_{p,T₀}` (also depending on `b, E`); for every `τ ∈ (0, T₀]` and
every `ClockSequence τ E` with all energies `E`:
`limsup_j n⁻¹Σ_{k<n} E|Z_{n;k} - d|^{2p} ≤ Cτ^p` and `limsup_j E|M_W - d|^{2p} ≤ Cτ^p`. -/
def TaggedFlatFixedEnergy : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ p : ℕ, 0 < p → ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E,
      (∀ j, s.energy j = E) →
      limsup (fun j => ((s.n j : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (s.n j),
          ∫⁻ x, ENNReal.ofReal
              (|lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x - dStar b| ^ (2 * p))
            ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p) ∧
      limsup (fun j => ∫⁻ x, ENNReal.ofReal (|rescaledClock b s j x - dStar b| ^ (2 * p))
          ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p)

/-- The tagged convex order theorem, energy-uniform reading. Fixed `0 < b < 1/2` and a bulk
energy `-2 < E < 2`: for every `s > 0` and every tagged sequence (`k_j/W_j → s`, `n_j/W_j → τ`,
moving energies `e_j → E`) the limiting-law clauses `TcoLimitLawClauses` hold (convex polynomial
comparison with geometric Brownian motion at time `τ - s`, mean `d`, convergence of all fixed
moments); and the averaged clause holds in the energy-uniform form `LmfTaggedFlat`. -/
def TaggedConvexOrderStatement : Prop :=
  (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, TcoLimitLawClauses b σ) ∧ LmfTaggedFlat

/-- The tagged convex order theorem at a fixed energy `E`: `TaggedConvexOrderStatement` for
constant energies. -/
def TaggedConvexOrderFixedStatement : Prop :=
  (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcoLimitLawClauses b σ) ∧
    TaggedFlatFixedEnergy

end BlockBand.Endpoints
