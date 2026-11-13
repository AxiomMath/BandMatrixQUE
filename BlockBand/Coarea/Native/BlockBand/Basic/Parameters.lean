module

public import BlockBand.Coarea.Native.BlockBand.CriticalSequences

/-!
# Admissible finite parameters and critical sequences

The total dimension is `L = nW`. Both the finite ratio and every variance
parameter use real division. The physical ring has no parity requirement.
The parameter structure fixes `b` before evaluating the integer sequence, and
the critical ratio may be zero without forcing `n → ∞`.

The endpoint filters are the right-sided real filter `𝓝[τ > 0] 0` and the
real filter `atTop`, **after** the positive finite-ratio critical family.
The endpoint statements below only specialize explicit convergence hypotheses.
They neither prove those hypotheses for this model nor exchange the order
of limits. There is no matrix probability law, Gaussian construction,
eigenvector selection or QUE estimate here.
-/

@[expose] public section

set_option autoImplicit false

namespace CoareaNative.BlockBand

open Filter Topology

/-- The finite model parameters: `n ≥ 4`, `W ≥ 1` and `0 < b < 1/2`
(definitionally `Conventions.ModelParameters`). -/
abbrev Params := Conventions.ModelParameters

/-- Critical sequences with limiting ratio `τ` (definitionally `CriticalSequence τ`).
They permit `τ = 0`, nonmonotone widths, and bounded block count. -/
abbrev CriticalSeq (τ : ℝ) := CriticalSequence τ

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

/-- The diagonal weight is strictly below one. -/
theorem c_lt_one (p : Params) : p.c < 1 := p.diagonalWeight_lt_one

/-- The three block weights sum to one. -/
theorem c_add_two_b (p : Params) : p.c + 2 * p.b = 1 :=
  Conventions.diagonalWeight_add_two_b p.b

/-- Explicit nonzero cyclic modulus. -/
theorem nNeZero (p : Params) : NeZero p.n := ⟨p.n_ne_zero⟩

/-- Explicit nonzero width. -/
theorem widthNeZero (p : Params) : NeZero p.W := ⟨Nat.ne_of_gt p.W_pos⟩

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

/-- Finite admissible ratios are positive; their limit may be zero. -/
theorem ratio_pos (p : Params) : 0 < p.ratio :=
  Conventions.criticalRatio_pos p

/-- The exact equality `n/W = L/W²`. -/
theorem ratio_eq_dimension_div_sq (p : Params) :
    p.ratio = (p.L : ℝ) / (p.W : ℝ) ^ 2 :=
  Conventions.criticalRatio_eq_dimension_div_sq p.n p.W p.W_pos

/-- A finite ratio ceiling is the dimension bound `n ≤ TW`;
`T` is an external real parameter, not selected from the sampled matrix. -/
theorem ratio_le_iff (p : Params) (T : ℝ) :
    p.ratio ≤ T ↔ (p.n : ℝ) ≤ T * (p.W : ℝ) :=
  Conventions.criticalRatio_le_iff p.n p.W p.W_pos T

/-- Diagonal-block total entry variance is `c/W`; a diagonal
entry is real with this variance, not half of it. This is numerical data only. -/
noncomputable abbrev diagonalVariance (p : Params) : ℝ :=
  Conventions.diagonalEntryVariance p.b p.W

/-- Forward-bond total complex entry variance is `b/W`. -/
noncomputable abbrev bondVariance (p : Params) : ℝ :=
  Conventions.bondEntryVariance p.b p.W

/-- Diagonal total entry variance is positive. -/
theorem diagonalVariance_pos (p : Params) : 0 < p.diagonalVariance :=
  Conventions.diagonalEntryVariance_pos p

/-- Bond total entry variance is positive. -/
theorem bondVariance_pos (p : Params) : 0 < p.bondVariance :=
  Conventions.bondEntryVariance_pos p

/-- Exact numerical row normalization, before a law is constructed.
Each of the three blocks has width `W`. -/
theorem variance_normalization (p : Params) :
    (p.W : ℝ) * (p.diagonalVariance + 2 * p.bondVariance) = 1 :=
  Conventions.rowVariance_normalization p.b p.W p.W_pos

end Params

namespace CriticalSeq

/-- Evaluate the admissible finite model at an index after fixing `b`. -/
def modelAt {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) : Params :=
  s.parameters b hb hbhalf j

/-- The finite model has exactly the original sequence's block count. -/
@[simp] theorem modelAt_n {τ : ℝ} (s : CriticalSeq τ) (b : ℝ) (hb : 0 < b)
    (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).n = s.n j := rfl

/-- The finite model has exactly the original sequence's width. -/
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

/-- The finite model preserves the original ratio exactly. -/
@[simp] theorem modelAt_ratio {τ : ℝ} (s : CriticalSeq τ) (b : ℝ)
    (hb : 0 < b) (hbhalf : b < 1 / 2) (j : ℕ) :
    (modelAt s b hb hbhalf j).ratio = s.ratio j := rfl

/-- At fixed variance, the ratios of the finite models converge to the same sequence
parameter. No probability-law convergence is asserted. -/
theorem modelAt_ratio_tendsto {τ : ℝ} (s : CriticalSeq τ) (b : ℝ)
    (hb : 0 < b) (hbhalf : b < 1 / 2) :
    Tendsto (fun j => (modelAt s b hb hbhalf j).ratio) atTop (𝓝 τ) :=
  s.ratio_tendsto

/-- Total integer dimension diverges because `L ≥ 4W`, even for
the zero-ratio bounded-block regime. No `n → ∞` assumption is introduced. -/
theorem dimension_tendsto {τ : ℝ} (s : CriticalSeq τ) :
    Tendsto (fun j => s.n j * s.W j) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [s.eventually_width_ge M] with j hj
  have hn : 1 ≤ s.n j := le_trans (by norm_num) (s.n_ge_four j)
  exact hj.trans (by simpa using Nat.mul_le_mul_right (s.W j) hn)

/-- The real total dimensions diverge under the same integer sequence.
The real cast is explicit and does not add a convergence rate. -/
theorem real_dimension_tendsto {τ : ℝ} (s : CriticalSeq τ) :
    Tendsto (fun j => ((s.n j * s.W j : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (dimension_tendsto s)

/-- The bounded-block critical sequence: its limiting ratio is zero while its block count
stays four. -/
noncomputable abbrev boundedBlocks : CriticalSeq 0 := CriticalSequence.boundedBlocks

end CriticalSeq

/-- The outer small-ratio filter, approached within positive ratios
after the critical law. It is not the integer width filter. -/
abbrev smallRatioFilter : Filter ℝ := 𝓝[Set.Ioi 0] 0

/-- The outer large-ratio filter on the real ratio parameter,
after the critical law. It is not any selected finite-model sequence. -/
abbrev largeRatioFilter : Filter ℝ := atTop

/-- The width-sequence index filter is on naturals,
unlike either endpoint ratio filter. -/
abbrev criticalWidthFilter : Filter ℕ := atTop

/-- Specialize a small-ratio endpoint hypothesis to the named filters. This extracts an
explicit assumption; it does not prove it. -/
theorem smallRatioEndpoint_of_contract {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X} {endpoint : κ → X}
    (h : CriticalThenSmallRatio finite critical endpoint) (fixed : κ) :
    Tendsto (critical fixed) smallRatioFilter (𝓝 (endpoint fixed)) :=
  h.outer fixed

/-- Specialize a large-ratio endpoint hypothesis without
inferring a diagonal `W,n/W` limit of the finite model. -/
theorem largeRatioEndpoint_of_contract {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X} {endpoint : κ → X}
    (h : CriticalThenLargeRatio finite critical endpoint) (fixed : κ) :
    Tendsto (critical fixed) largeRatioFilter (𝓝 (endpoint fixed)) :=
  h.outer fixed

/-- A critical family converging along every `CriticalSeq τ` at a strictly positive fixed
finite ratio converges along the finite models. -/
theorem criticalFamily_along_params {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X}
    (h : CriticalFamilyTendsto finite critical) (fixed : κ)
    {τ : ℝ} (hτ : 0 < τ) (s : CriticalSeq τ) :
    Tendsto (fun j => finite fixed (s.n j) (s.W j))
      criticalWidthFilter (𝓝 (critical fixed τ)) :=
  h.along fixed hτ s

end CoareaNative.BlockBand
