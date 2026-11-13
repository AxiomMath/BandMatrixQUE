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

namespace ERNative.BlockBand.Conventions

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

/-- Introduction: total matrix dimension `L = nW`, including the block multiplicity. -/
def dimension (n W : ℕ) : ℕ := n * W

/-- A site is a cyclic block label modulo `n`
and an internal coordinate. The internal `Fin W` value `a₀` represents the
one-based label `a = a₀ + 1`. This convention needs no parity assumption on `n`. -/
abbrev Site (n W : ℕ) := ZMod n × Fin W

/-- For positive `n`, the canonical representative of a cyclic
block label is a `Fin n` value, and conversely a `Fin n` value is cast modulo `n`.
This exposes the representative used by row-major flattening without replacing
cyclic arithmetic by bounded arithmetic. -/
def cyclicBlockEquivFin (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun k := ⟨k.val, k.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv k := ZMod.natCast_zmod_val k
  right_inv k := by
    apply Fin.ext
    exact ZMod.val_cast_of_lt k.isLt

/-- Row-major site flattening identifies
`(ZMod n) × Fin W` with `Fin (nW)`. The block representative is the slow coordinate,
so `(k,a₀)` has zero-based flat index `a₀ + W k₀`. -/
def siteEquivFin (n W : ℕ) [NeZero n] : Site n W ≃ Fin (dimension n W) :=
  (Equiv.prodCongr (cyclicBlockEquivFin n) (Equiv.refl _)).trans finProdFinEquiv

/-- The row-major equivalence has the advertised explicit zero-based index. -/
@[simp] theorem siteEquivFin_apply_val (n W : ℕ) [NeZero n] (x : Site n W) :
    (siteEquivFin n W x).val = x.2.val + W * x.1.val := by
  rfl

/-- Diagonal-block weight `c = 1 - 2b`; this is not an entry variance. -/
def diagonalWeight (b : ℝ) : ℝ := 1 - 2 * b

namespace ModelParameters

/-- The total matrix dimension for an admissible finite ring. -/
def L (p : ModelParameters) : ℕ := dimension p.n p.W

/-- Both block and bond randomness require positive dimensions, uniformly for all
admissible finite parameters; no limit order is involved. -/
theorem n_pos (p : ModelParameters) : 0 < p.n := by
  exact lt_of_lt_of_le (by norm_num) p.n_ge_four

/-- The lower bound `n ≥ 4` supplies the positive modulus
needed by `cyclicBlockEquivFin` and `siteEquivFin`. -/
theorem n_ne_zero (p : ModelParameters) : p.n ≠ 0 :=
  Nat.ne_of_gt p.n_pos

/-- The row-major site equivalence specialized to admissible model parameters.
The proof uses `n ≥ 4`; it introduces no additional modulus hypothesis downstream. -/
def siteIndexEquiv (p : ModelParameters) : Site p.n p.W ≃ Fin p.L := by
  letI : NeZero p.n := ⟨p.n_ne_zero⟩
  exact siteEquivFin p.n p.W

/-- The parameter-specialized equivalence retains the row-major formula. -/
@[simp] theorem siteIndexEquiv_apply_val (p : ModelParameters) (x : Site p.n p.W) :
    (p.siteIndexEquiv x).val = x.2.val + p.W * x.1.val := by
  let _ : NeZero p.n := ⟨p.n_ne_zero⟩
  rfl

/-- The width is a positive integer, not a possibly vanishing real parameter. -/
theorem W_pos (p : ModelParameters) : 0 < p.W := by
  exact p.W_ge_one

/-- The finite matrix dimension is positive for every admissible ring. -/
theorem L_pos (p : ModelParameters) : 0 < p.L := by
  exact Nat.mul_pos p.n_pos p.W_pos

/-- The diagonal-block weight is positive for fixed `b < 1/2`. -/
theorem diagonalWeight_pos (p : ModelParameters) : 0 < diagonalWeight p.b := by
  unfold diagonalWeight
  linarith [p.b_lt_half]

end ModelParameters

/-- The three block weights sum to one before division by width. -/
theorem diagonalWeight_add_two_b (b : ℝ) : diagonalWeight b + 2 * b = 1 := by
  unfold diagonalWeight
  ring

/-- Introduction: casts commute with the total-dimension product. -/
theorem dimension_cast (n W : ℕ) : (dimension n W : ℝ) = (n : ℝ) * (W : ℝ) := by
  simp [dimension]

/-- The dimensionless finite-ring ratio `τ_W = n/W`. Both inputs are
integers but division is real; this definition does not assert convergence. -/
noncomputable def criticalRatio (n W : ℕ) : ℝ := (n : ℝ) / (W : ℝ)

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

/-- Stochastic domination: probability of the displayed tail event.
The generic `N` is not the paper's block count `n`, width `W`, or dimension `L`.
The probability law may depend on every displayed parameter. Stochastic domination
requires the random-variable measurability that makes this a probability rather
than merely the measure's outer value. -/
noncomputable def dominationTailProbability {κ ι Ω : Type*} [MeasurableSpace Ω]
    (μ : κ → ι → ℕ → ProbabilityMeasure Ω)
    (X Y : κ → ι → ℕ → Ω → ℝ) (fixed : κ) (ε : ℝ) (i : ι) (N : ℕ) : ENNReal :=
  (μ fixed i N : Measure Ω) (dominationTailEvent X Y fixed ε i N)

/-- Stochastic domination: precise convention for `X ≺ Y`.

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

end ERNative.BlockBand.Conventions
