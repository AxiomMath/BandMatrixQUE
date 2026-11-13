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
public import Lean.Elab.Tactic.Omega
public import Mathlib

/-!
# Scalar and site conventions for Gaussian block-band matrices

The parameters `n ≥ 4`, `W ≥ 1` and `0 < b < 1/2` of the cyclic block-band model, its
dimension `L = nW`, the diagonal block weight `c = 1 - 2b`, and the real critical ratio
`n/W = L/W²`. All variance and rescaling formulas use explicit real casts.

The site `(k,a)` of the paper is represented by `ZMod n × Fin W`: `k` is cyclic,
while Lean's zero-based internal coordinate corresponds to the label `a = 1,…,W`. The
row-major flattening is `a₀ + W k₀`. Every result here is exact algebra.
-/

@[expose] public section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.Conventions

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

/-- Diagonal-block weight `c = 1 - 2b`; this is not entry variance. -/
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

/-- The parameter-specialized equivalence retains the source row-major formula. -/
@[simp] theorem siteIndexEquiv_apply_val (p : ModelParameters) (x : Site p.n p.W) :
    (p.siteIndexEquiv x).val = x.2.val + p.W * x.1.val := by
  let _ : NeZero p.n := ⟨p.n_ne_zero⟩
  rfl

/-- Width is a positive integer, not a possibly vanishing real parameter. -/
theorem W_pos (p : ModelParameters) : 0 < p.W := by
  exact p.W_ge_one

/-- The finite matrix dimension is positive for every admissible ring. -/
theorem L_pos (p : ModelParameters) : 0 < p.L := by
  exact Nat.mul_pos p.n_pos p.W_pos

/-- Real dimension used in variance and unfolding formulas is nonzero. -/
theorem real_L_pos (p : ModelParameters) : 0 < (p.L : ℝ) := by
  exact_mod_cast p.L_pos

/-- Real width used as denominator in the model is strictly positive. -/
theorem real_W_pos (p : ModelParameters) : 0 < (p.W : ℝ) := by
  exact_mod_cast p.W_pos

/-- Diagonal-block weight is positive for fixed `b < 1/2`. -/
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

/-- Dimensionless finite-ring ratio `τ_W = n/W`. Both inputs are
integers but division is real; this definition does not assert convergence. -/
noncomputable def criticalRatio (n W : ℕ) : ℝ := (n : ℝ) / (W : ℝ)

/-- Exactly `n/W = L/W²` when the width is positive. -/
theorem criticalRatio_eq_dimension_div_sq (n W : ℕ) (hW : 0 < W) :
    criticalRatio n W = (dimension n W : ℝ) / (W : ℝ) ^ 2 := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  simp only [criticalRatio, dimension_cast]
  field_simp

end BlockBand.Adapters.ErdosRiabov.CyclicModel.Conventions
