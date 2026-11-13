module

public import BlockBand.Native.ErdosRiabov.BlockBand.CriticalSequences

/-!
# Admissible finite parameters and critical-sequence adapters

The total dimension is `L = nW`. Both the finite ratio and every variance
parameter use real division. The physical ring has no parity requirement.
The parameter API fixes `b` before evaluating the integer sequence, and
the critical ratio may be zero without forcing `n → ∞`. Explicit nonzero
dimension witnesses are provided; block embeddings, projections and
cardinality are treated with the site indices.

The endpoint filters are the right-sided real filter `𝓝[τ > 0] 0` and the
real filter `atTop`, **after** the positive finite-ratio critical family.
The adapters below only specialize the explicit convergence hypotheses of `CriticalSeq`.
They neither prove those hypotheses for this model nor exchange the order
of limits. There is no matrix probability law, Gaussian construction,
eigenvector selection or QUE estimate here.
-/

@[expose] public section

set_option autoImplicit false

namespace ERNative.BlockBand

open Filter Topology

/-- The finite model parameters `n ≥ 4`, `W ≥ 1`, `0 < b < 1/2`
(`Conventions.ModelParameters`). -/
abbrev Params := Conventions.ModelParameters

/-- Critical sequences with ratio `n/W → τ` (`CriticalSequence`). It permits `τ = 0`,
nonmonotone widths, and bounded block count. -/
abbrev CriticalSeq (τ : ℝ) := CriticalSequence τ

namespace Params

/-- Construct finite parameters from the exact model inequalities.
There is no parity or limiting-ratio assumption and no matrix-law input. -/
def ofDimensions (n W : ℕ) (b : ℝ) (hn : 4 ≤ n) (hW : 1 ≤ W)
    (hb : 0 < b) (hbhalf : b < 1 / 2) : Params :=
  ⟨n, W, b, hn, hW, hb, hbhalf⟩

/-- The constructor retains the integer block count. -/
@[simp] theorem ofDimensions_n (n W : ℕ) (b : ℝ) (hn : 4 ≤ n)
    (hW : 1 ≤ W) (hb : 0 < b) (hbhalf : b < 1 / 2) :
    (ofDimensions n W b hn hW hb hbhalf).n = n := rfl

/-- The constructor retains the integer block width. -/
@[simp] theorem ofDimensions_W (n W : ℕ) (b : ℝ) (hn : 4 ≤ n)
    (hW : 1 ≤ W) (hb : 0 < b) (hbhalf : b < 1 / 2) :
    (ofDimensions n W b hn hW hb hbhalf).W = W := rfl

/-- The constructor retains the fixed bond parameter. -/
@[simp] theorem ofDimensions_b (n W : ℕ) (b : ℝ) (hn : 4 ≤ n)
    (hW : 1 ≤ W) (hb : 0 < b) (hbhalf : b < 1 / 2) :
    (ofDimensions n W b hn hW hb hbhalf).b = b := rfl

/-- The diagonal block weight `c = 1 - 2b` (not an entry variance). -/
abbrev c (p : Params) : ℝ := Conventions.diagonalWeight p.b

/-- The diagonal weight is strictly positive at every finite model.
There is no constant uniform up to `b = 1/2`. -/
theorem c_pos (p : Params) : 0 < p.c := p.diagonalWeight_pos

/-- The three block weights sum to one. -/
theorem c_add_two_b (p : Params) : p.c + 2 * p.b = 1 :=
  Conventions.diagonalWeight_add_two_b p.b

/-- Explicit nonzero cyclic modulus for the site indices. -/
theorem nNeZero (p : Params) : NeZero p.n := ⟨p.n_ne_zero⟩

/-- Explicit nonzero total dimension `L = nW`. -/
theorem dimensionNeZero (p : Params) : NeZero p.L := ⟨Nat.ne_of_gt p.L_pos⟩

/-- Total dimension is exactly the block count times width. -/
@[simp] theorem L_eq (p : Params) : p.L = p.n * p.W := rfl

/-- Real dimension uses explicit casts of both integer dimensions. -/
theorem real_L_eq (p : Params) : (p.L : ℝ) = (p.n : ℝ) * (p.W : ℝ) :=
  Conventions.dimension_cast p.n p.W

/-- The whole ring contains at least four blocks of its width. -/
theorem four_mul_width_le_dimension (p : Params) : 4 * p.W ≤ p.L :=
  Nat.mul_le_mul_right p.W p.n_ge_four

/-- Real ratio, not natural-number division. -/
noncomputable abbrev ratio (p : Params) : ℝ := Conventions.criticalRatio p.n p.W

end Params

namespace CriticalSeq

/-- Evaluate the admissible finite model at an index after
fixing `b`. This is an adapter, not a new sequence representation. -/
def modelAt {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) : Params :=
  s.parameters b hb hbhalf j

/-- The finite adapter has exactly the original sequence's block count. -/
@[simp] theorem modelAt_n {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).n = s.n j := rfl

/-- The finite adapter has exactly the original sequence's width. -/
@[simp] theorem modelAt_W {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).W = s.W j := rfl

/-- The bond parameter is the same externally fixed `b` at every index. -/
@[simp] theorem modelAt_b {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).b = b := rfl

/-- The total dimension has not lost the block multiplicity. -/
@[simp] theorem modelAt_dimension {τ : ℝ} (s : CriticalSeq τ) (b : ℝ)
    (hb : 0 < b) (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).L = s.n j * s.W j := rfl

/-- The model adapter preserves the original ratio exactly. -/
@[simp] theorem modelAt_ratio {τ : ℝ} (s : CriticalSeq τ) (b : ℝ)
    (hb : 0 < b) (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).ratio = s.ratio j := rfl

end CriticalSeq

end ERNative.BlockBand
