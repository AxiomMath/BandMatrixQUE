module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CriticalSequences
public import Mathlib

/-!
# Admissible finite parameters

The constructor of the model parameters from `n ≥ 4`, `W ≥ 1` and `b`, the diagonal
weight `c = 1 - 2b` with `c + 2b = 1`, nonzero witnesses for `n` and `L = nW`, and the
real ratio `n/W = L/W²`. The physical ring has no parity requirement.
-/

@[expose] public section

set_option autoImplicit false

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel

open Filter Topology

/-- The finite model parameters: `n ≥ 4`, `W ≥ 1` and `0 < b < 1/2`
(definitionally `Conventions.ModelParameters`). -/
abbrev Params := Conventions.ModelParameters

namespace Params

/-- Construct finite parameters from the exact inequalities of the model.
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

/-- The diagonal weight `c = 1 - 2b`, not entry variance. -/
abbrev c (p : Params) : ℝ := Conventions.diagonalWeight p.b

/-- The diagonal weight is strictly positive at every finite model.
There is no constant uniform up to `b = 1/2`. -/
theorem c_pos (p : Params) : 0 < p.c := p.diagonalWeight_pos

/-- The three block weights sum to one. -/
theorem c_add_two_b (p : Params) : p.c + 2 * p.b = 1 :=
  Conventions.diagonalWeight_add_two_b p.b

/-- Explicit nonzero cyclic modulus. -/
theorem nNeZero (p : Params) : NeZero p.n := ⟨p.n_ne_zero⟩

/-- Explicit nonzero total dimension `L = nW`. -/
theorem dimensionNeZero (p : Params) : NeZero p.L := ⟨Nat.ne_of_gt p.L_pos⟩

/-- Real ratio, not natural-number division. -/
noncomputable abbrev ratio (p : Params) : ℝ := Conventions.criticalRatio p.n p.W

/-- The exact equality `n/W = L/W²`. -/
theorem ratio_eq_dimension_div_sq (p : Params) :
    p.ratio = (p.L : ℝ) / (p.W : ℝ) ^ 2 :=
  Conventions.criticalRatio_eq_dimension_div_sq p.n p.W p.W_pos

end Params

namespace CriticalSeq

end CriticalSeq

end BlockBand.Adapters.ErdosRiabov.CyclicModel
