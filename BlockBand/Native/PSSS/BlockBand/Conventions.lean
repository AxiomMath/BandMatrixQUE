module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Scalar and rank conventions for Gaussian block-band matrices

All dimensions are natural numbers; all variance and spectral rescaling formulas use
explicit real casts. The site `(k,a)` is represented by
`ZMod n × Fin W`: `k` is cyclic, while Lean's zero-based internal coordinate
corresponds to the label `a = 1,…,W`. The row-major flattening is
`a₀ + W k₀`, and adding one gives the one-based total-site rank. A `Fin L`
eigenvalue index is likewise converted to a one-based rank before
division by `L`.

Gaussian variance conventions here specify numerical parameters, not random variables
or probability laws: a circular complex entry of total variance `s` has component
variances `s/2`, whereas a real diagonal entry has variance `s` itself.

This module fixes the cyclic site equivalence but does not define block projections,
the matrix law, selected eigenvectors, the trace/norm calculus, or any
QUE/critical-limit theorem. Every finite-dimensional result here is exact algebra, with
no covariance assumption. The stochastic-domination declaration near the end is only the
quantifier convention of the paper, not an estimate about the block-band model.

## Asymptotic conventions

The limits `W → ∞`, `n/W → τ` are joint integer-sequence limits with `b`,
bulk margin, and energy fixed before the sequence. The generic domination scale `N`
below is deliberately not identified with the parameters `n`, `W`, or `L`.
-/

@[expose] public section

namespace PSSSNative.BlockBand.Conventions

open MeasureTheory

/-- Introduction, block-ring paragraph: `n ≥ 4`, `W ≥ 1`, and fixed `0 < b < 1/2`.
This is finite parameter data, not a critical sequence or a Gaussian law. -/
structure ModelParameters where
  n : ℕ
  W : ℕ
  b : ℝ
  n_ge_four : 4 ≤ n
  W_ge_one : 1 ≤ W
  b_pos : 0 < b
  b_lt_half : b < 1 / 2

namespace ModelParameters

/-- Both block and bond randomness require positive dimensions, uniformly for all
admissible finite parameters; no limit order is involved. -/
theorem n_pos (p : ModelParameters) : 0 < p.n := by
  exact lt_of_lt_of_le (by norm_num) p.n_ge_four

/-- The lower bound `n ≥ 4` supplies the positive modulus
needed by `cyclicBlockEquivFin` and `siteEquivFin`. -/
theorem n_ne_zero (p : ModelParameters) : p.n ≠ 0 :=
  Nat.ne_of_gt p.n_pos

end ModelParameters

/-- Stochastic domination: the tail event
`X > N^ε Y` for fixed external parameters `fixed`, declared-uniform deterministic
parameters `i`, and asymptotic scale `N`. -/
def dominationTailEvent {κ ι Ω : Type*}
    (X Y : κ → ι → ℕ → Ω → ℝ) (fixed : κ) (ε : ℝ) (i : ι) (N : ℕ) : Set Ω :=
  {ω | X fixed i N ω > Real.rpow (N : ℝ) ε * Y fixed i N ω}

/-- Measurable random variables give a measurable tail event. This lemma
prevents `dominationTailProbability` from silently being used as outer probability. -/
theorem dominationTailEvent_measurable {κ ι Ω : Type*} [MeasurableSpace Ω]
    {X Y : κ → ι → ℕ → Ω → ℝ} {fixed : κ} {ε : ℝ} {i : ι} {N : ℕ}
    (hX : Measurable (X fixed i N)) (hY : Measurable (Y fixed i N)) :
    MeasurableSet (dominationTailEvent X Y fixed ε i N) := by
  exact measurableSet_lt (measurable_const.mul hY) hX

/-- Probability of the displayed tail event.
The generic `N` is not the paper's block count `n`, width `W`, or dimension `L`.
The probability law may depend on every displayed parameter. Stochastic domination
requires the random-variable measurability that makes this a probability rather
than merely the measure's outer value. -/
noncomputable def dominationTailProbability {κ ι Ω : Type*} [MeasurableSpace Ω]
    (μ : κ → ι → ℕ → ProbabilityMeasure Ω)
    (X Y : κ → ι → ℕ → Ω → ℝ) (fixed : κ) (ε : ℝ) (i : ι) (N : ℕ) : ENNReal :=
  (μ fixed i N : Measure Ω) (dominationTailEvent X Y fixed ε i N)

/-- Precise convention for `X ≺ Y`.

For each already-fixed `fixed`, both positive exponents `ε,D` are chosen before
the dimension scale tends to infinity. A single cutoff `N₀`, allowed to depend on
`fixed,ε,D`, then works for every declared-uniform deterministic parameter `i`.
The requirement `1 ≤ N₀` avoids the meaningless zero base with a negative real
power. Measurability of both real random variables is part of the definition,
so every displayed tail set is measurable by `dominationTailEvent_measurable`.
No nonnegativity premise is added. This predicate is only the convention; it carries no
asymptotic estimate. -/
noncomputable def StochasticDominationConvention {κ ι Ω : Type*} [MeasurableSpace Ω]
    (μ : κ → ι → ℕ → ProbabilityMeasure Ω)
    (X Y : κ → ι → ℕ → Ω → ℝ) (fixed : κ) : Prop :=
  (∀ i N, Measurable (X fixed i N) ∧ Measurable (Y fixed i N)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ i : ι,
        dominationTailProbability μ X Y fixed ε i N ≤
          ENNReal.ofReal (Real.rpow (N : ℝ) (-D))

/-- Stochastic domination exposes measurability of both random variables
at every declared-uniform parameter and dimension. -/
theorem StochasticDominationConvention.measurable {κ ι Ω : Type*} [MeasurableSpace Ω]
    {μ : κ → ι → ℕ → ProbabilityMeasure Ω}
    {X Y : κ → ι → ℕ → Ω → ℝ} {fixed : κ}
    (h : StochasticDominationConvention μ X Y fixed) (i : ι) (N : ℕ) :
    Measurable (X fixed i N) ∧ Measurable (Y fixed i N) :=
  h.1 i N

/-- Unpack stochastic domination at fixed positive `ε,D`. The returned cutoff is
still uniform in the deterministic family `i`. -/
theorem StochasticDominationConvention.bound {κ ι Ω : Type*} [MeasurableSpace Ω]
    {μ : κ → ι → ℕ → ProbabilityMeasure Ω}
    {X Y : κ → ι → ℕ → Ω → ℝ} {fixed : κ}
    (h : StochasticDominationConvention μ X Y fixed) {ε D : ℝ}
    (hε : 0 < ε) (hD : 0 < D) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ i : ι,
      dominationTailProbability μ X Y fixed ε i N ≤
        ENNReal.ofReal (Real.rpow (N : ℝ) (-D)) :=
  h.2 ε hε D hD

end PSSSNative.BlockBand.Conventions
