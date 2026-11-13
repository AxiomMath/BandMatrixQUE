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
explicit real casts. A site `(k,a)` of the block ring is represented by
`ZMod n × Fin W`: `k` is cyclic, while Lean's zero-based internal coordinate
corresponds to the one-based label `a = 1,…,W` of the paper. The row-major flattening is
`a₀ + W k₀`, and adding one gives the one-based total-site rank. A `Fin L`
eigenvalue index is likewise converted to a one-based rank before division by `L`.

Gaussian variance conventions here specify numerical parameters, not random variables
or probability laws: a circular complex entry of total variance `s` has component
variances `s/2`, whereas a real diagonal entry has variance `s` itself.

This file fixes the cyclic site equivalence but does not define block projections,
the matrix law, selected eigenvectors, the trace and norm calculus, or any
QUE or critical-limit theorem. Every finite-dimensional result here is exact algebra.
The stochastic-domination declaration near the end only fixes the quantifier
convention of the paper; it is not an estimate about the block-band model.

## Derivative and asymptotic boundary

The limits `W → ∞`, `n/W → τ` are joint integer-sequence limits with `b`,
bulk margin, and energy fixed before the sequence. The generic domination scale `N`
below is deliberately not identified with the model parameters `n`, `W`, or `L`.
-/

@[expose] public section

namespace CoareaNative.BlockBand.Conventions

open MeasureTheory

/-- Parameters of the block ring: `n ≥ 4`, `W ≥ 1`, and fixed `0 < b < 1/2`.
This is finite parameter data, not a critical sequence or a Gaussian law. -/
structure ModelParameters where
  n : ℕ
  W : ℕ
  b : ℝ
  n_ge_four : 4 ≤ n
  W_ge_one : 1 ≤ W
  b_pos : 0 < b
  b_lt_half : b < 1 / 2

/-- Total matrix dimension `L = nW`, including the block multiplicity. -/
def dimension (n W : ℕ) : ℕ := n * W

/-- A site is a cyclic block label modulo `n`
and an internal coordinate. The internal `Fin W` value `a₀` represents the paper's
one-based label `a = a₀ + 1`. This convention needs no parity assumption on `n`. -/
abbrev Site (n W : ℕ) := ZMod n × Fin W

/-- Convert Lean's zero-based internal coordinate to the one-based
label in `{1,…,W}`. This is unrelated to the eigenvalue rank in `sourceRank`. -/
def sourceInternalLabel {W : ℕ} (a : Fin W) : ℕ := a.val + 1

/-- Every source internal label `1 ≤ a ≤ W` has a canonical
zero-based `Fin W` implementation coordinate. -/
def internalIndexOfSourceLabel {W a : ℕ} (ha0 : 1 ≤ a) (haW : a ≤ W) : Fin W :=
  ⟨a - 1, by omega⟩

/-- The source-to-implementation conversion preserves a valid one-based label. -/
theorem sourceInternalLabel_internalIndexOfSourceLabel {W a : ℕ}
    (ha0 : 1 ≤ a) (haW : a ≤ W) :
    sourceInternalLabel (internalIndexOfSourceLabel ha0 haW) = a := by
  simp [sourceInternalLabel, internalIndexOfSourceLabel]
  omega

/-- The implementation-to-source conversion preserves every `Fin W` coordinate. -/
theorem internalIndexOfSourceLabel_sourceInternalLabel {W : ℕ} (a : Fin W) :
    internalIndexOfSourceLabel (Nat.succ_le_succ (Nat.zero_le _))
        (Nat.succ_le_of_lt a.isLt) = a := by
  apply Fin.ext
  simp [internalIndexOfSourceLabel]

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

/-- Addition of block labels remains addition modulo the source parameter `n`. -/
theorem cyclicBlockEquivFin_add_val (n : ℕ) [NeZero n] (k l : ZMod n) :
    (cyclicBlockEquivFin n (k + l)).val = (k.val + l.val) % n :=
  ZMod.val_add k l

/-- Row-major site flattening identifies
`(ZMod n) × Fin W` with `Fin (nW)`. The block representative is the slow coordinate,
so `(k,a₀)` has zero-based flat index `a₀ + W k₀`. -/
def siteEquivFin (n W : ℕ) [NeZero n] : Site n W ≃ Fin (dimension n W) :=
  (Equiv.prodCongr (cyclicBlockEquivFin n) (Equiv.refl _)).trans finProdFinEquiv

/-- The row-major equivalence has the advertised explicit zero-based index. -/
@[simp] theorem siteEquivFin_apply_val (n W : ℕ) [NeZero n] (x : Site n W) :
    (siteEquivFin n W x).val = x.2.val + W * x.1.val := by
  rfl

/-- Source-style flattened site ranks are one-based, in contrast
to the `Fin (nW)` implementation index. -/
def sourceSiteRank (n W : ℕ) [NeZero n] (x : Site n W) : ℕ :=
  (siteEquivFin n W x).val + 1

/-- Explicit source formula for the one-based flattened site rank. -/
theorem sourceSiteRank_eq (n W : ℕ) [NeZero n] (x : Site n W) :
    sourceSiteRank n W x = x.2.val + W * x.1.val + 1 := by
  rfl

/-- Every represented site has a positive source-style rank. -/
theorem sourceSiteRank_pos (n W : ℕ) [NeZero n] (x : Site n W) :
    0 < sourceSiteRank n W x :=
  Nat.succ_pos _

/-- Every represented site rank is at most the total dimension `nW`. -/
theorem sourceSiteRank_le (n W : ℕ) [NeZero n] (x : Site n W) :
    sourceSiteRank n W x ≤ dimension n W :=
  Nat.succ_le_of_lt (siteEquivFin n W x).isLt

/-- Row-major source site ranks do not identify distinct cyclic sites. -/
theorem sourceSiteRank_injective (n W : ℕ) [NeZero n] :
    Function.Injective (sourceSiteRank n W) := by
  intro x y h
  apply (siteEquivFin n W).injective
  apply Fin.ext
  exact Nat.add_right_cancel h

/-- Diagonal-block weight `c = 1 - 2b`; this is not entry variance. -/
def diagonalWeight (b : ℝ) : ℝ := 1 - 2 * b

namespace ModelParameters

/-- The total matrix dimension for an admissible finite ring. -/
def L (p : ModelParameters) : ℕ := dimension p.n p.W

/-- Both block and bond randomness require positive dimensions, uniformly for all
admissible finite parameters; no limit order is involved. -/
theorem n_pos (p : ModelParameters) : 0 < p.n := by
  exact lt_of_lt_of_le (by norm_num) p.n_ge_four

/-- The source lower bound `n ≥ 4` supplies the positive modulus
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

/-- Real width used as denominator in the variance profile is strictly positive. -/
theorem real_W_pos (p : ModelParameters) : 0 < (p.W : ℝ) := by
  exact_mod_cast p.W_pos

/-- Diagonal-block weight is positive for fixed `b < 1/2`. -/
theorem diagonalWeight_pos (p : ModelParameters) : 0 < diagonalWeight p.b := by
  unfold diagonalWeight
  linarith [p.b_lt_half]

/-- The diagonal weight is below one because bonds have
strictly positive weight. No lower bound uniform in `b` is asserted. -/
theorem diagonalWeight_lt_one (p : ModelParameters) : diagonalWeight p.b < 1 := by
  unfold diagonalWeight
  linarith [p.b_pos]

end ModelParameters

/-- The three block weights sum to one before division by width. -/
theorem diagonalWeight_add_two_b (b : ℝ) : diagonalWeight b + 2 * b = 1 := by
  unfold diagonalWeight
  ring

/-- Casts commute with the total-dimension product. -/
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

/-- Positivity of the ratio for every admissible finite ring. -/
theorem criticalRatio_pos (p : ModelParameters) : 0 < criticalRatio p.n p.W := by
  unfold criticalRatio
  exact div_pos (by exact_mod_cast p.n_pos) p.real_W_pos

/-- The quantitative QUE range `n ≤ TW` is exactly a bound on the
real ratio; `T` is fixed before applying this equivalence at any finite ring. -/
theorem criticalRatio_le_iff (n W : ℕ) (hW : 0 < W) (T : ℝ) :
    criticalRatio n W ≤ T ↔ (n : ℝ) ≤ T * (W : ℝ) := by
  have hW' : 0 < (W : ℝ) := by exact_mod_cast hW
  exact div_le_iff₀ hW'

/-- Converts a zero-based `Fin L` index to source rank in `{1,…,L}`.
It does not select an eigenvector, handle repeated eigenvalues, or impose a law. -/
def sourceRank {L : ℕ} (α : Fin L) : ℕ := α.val + 1

/-- Every source rank is one-based. -/
theorem sourceRank_pos {L : ℕ} (α : Fin L) : 0 < sourceRank α := by
  exact Nat.succ_pos _

/-- The largest source rank is `L`, not `L-1`. -/
theorem sourceRank_le {L : ℕ} (α : Fin L) : sourceRank α ≤ L := by
  exact Nat.succ_le_of_lt α.isLt

/-- Rank conversion does not identify distinct finite eigenvalue indices. -/
theorem sourceRank_injective {L : ℕ} : Function.Injective (@sourceRank L) := by
  intro α β h
  apply Fin.ext
  exact Nat.add_right_cancel h

/-- Normalized deterministic rank uses the one-based numerator `α/L`. -/
noncomputable def rankFraction {L : ℕ} (α : Fin L) : ℝ :=
  (sourceRank α : ℝ) / (L : ℝ)

/-- Exact closed bulk inequalities. Admissibility of the fixed margin
`0 < θ < 1/2` is a separate hypothesis, not implicit in this predicate. -/
def IsBulkRank {L : ℕ} (θ : ℝ) (α : Fin L) : Prop :=
  θ ≤ rankFraction α ∧ rankFraction α ≤ 1 - θ

/-- A represented finite rank has strictly positive rank fraction. -/
theorem rankFraction_pos {L : ℕ} (α : Fin L) : 0 < rankFraction α := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt α.isLt)
  exact div_pos (by exact_mod_cast sourceRank_pos α) hL

/-- Normalized source ranks lie in `(0,1]`, with the final rank equal
to one and hence outside any positive-margin bulk. -/
theorem rankFraction_le_one {L : ℕ} (α : Fin L) : rankFraction α ≤ 1 := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt α.isLt)
  apply (div_le_iff₀ hL).2
  simpa using (show (sourceRank α : ℝ) ≤ (L : ℝ) by exact_mod_cast sourceRank_le α)

/-- The closed fractional inequalities are equivalent to unnormalized
rank inequalities; multiplying by `L` never reverses them. -/
theorem isBulkRank_iff {L : ℕ} (θ : ℝ) (α : Fin L) :
    IsBulkRank θ α ↔
      θ * (L : ℝ) ≤ (sourceRank α : ℝ) ∧
        (sourceRank α : ℝ) ≤ (1 - θ) * (L : ℝ) := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt α.isLt)
  exact and_congr (le_div_iff₀ hL) (div_le_iff₀ hL)

/-- A real diagonal entry has variance `c/W`;
the off-diagonal entries in its block have the same *total* complex variance. -/
noncomputable def diagonalEntryVariance (b : ℝ) (W : ℕ) : ℝ :=
  diagonalWeight b / (W : ℝ)

/-- A forward-bond entry has total circular complex variance `b/W`. -/
noncomputable def bondEntryVariance (b : ℝ) (W : ℕ) : ℝ := b / (W : ℝ)

/-- Each real component of a circular complex
Gaussian of total variance `s` has variance `s/2`. No independence or Gaussian
distribution is asserted by this numerical definition. -/
noncomputable def complexComponentVariance (s : ℝ) : ℝ := s / 2

/-- The two component variance parameters sum to total complex variance.
Variance additivity for random variables belongs to a Gaussian-law module. -/
theorem componentVariance_add (s : ℝ) :
    complexComponentVariance s + complexComponentVariance s = s := by
  unfold complexComponentVariance
  ring

/-- A positive complex-entry variance has strictly positive component variances. -/
theorem complexComponentVariance_pos {s : ℝ} (hs : 0 < s) :
    0 < complexComponentVariance s := by
  exact div_pos hs (by norm_num)

/-- Every admissible diagonal-block entry variance is positive. -/
theorem diagonalEntryVariance_pos (p : ModelParameters) :
    0 < diagonalEntryVariance p.b p.W :=
  div_pos p.diagonalWeight_pos p.real_W_pos

/-- Every admissible forward-bond entry variance is positive. -/
theorem bondEntryVariance_pos (p : ModelParameters) :
    0 < bondEntryVariance p.b p.W :=
  div_pos p.b_pos p.real_W_pos

/-- Normalized `d × d` GUE uses total entry variance `1/d`;
the diagonal variance is this number, whereas each off-diagonal real component
has half this number. This is a parameter, not a constructed probability law. -/
noncomputable def normalizedGUEEntryVariance (d : ℕ) : ℝ := 1 / (d : ℝ)

/-- Normalized GUE entry variance is positive at positive
finite dimension; dimension zero is deliberately not admissible for a law. -/
theorem normalizedGUEEntryVariance_pos {d : ℕ} (hd : 0 < d) :
    0 < normalizedGUEEntryVariance d :=
  div_pos (by norm_num) (by exact_mod_cast hd)

/-- Matrix notation: angle brackets mean `d⁻¹ Tr A`. All other
matrix traces remain Mathlib's unnormalized `Matrix.trace`. This convention
does not silently normalize block-local traces by the full dimension `nW`. -/
noncomputable def normalizedTrace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (d : ℂ)⁻¹ * Matrix.trace A

/-- The normalized trace is additive at fixed finite dimension. -/
theorem normalizedTrace_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, mul_add]

/-- Scalar multiplication does not change the trace dimension. -/
theorem normalizedTrace_smul {d : ℕ} (z : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    normalizedTrace (z • A) = z * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The identity's normalized trace is exactly one at positive
dimension. No statement about the zero-dimensional identity is asserted. -/
theorem normalizedTrace_one {d : ℕ} (hd : 0 < d) :
    normalizedTrace (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp [normalizedTrace, Matrix.trace_one, hd']

/-- Numerical row-variance normalization counts `W` entries in
each of three blocks. This is not a proof about a yet-unconstructed matrix law. -/
theorem rowVariance_normalization (b : ℝ) (W : ℕ) (hW : 0 < W) :
    (W : ℝ) * (diagonalEntryVariance b W + 2 * bondEntryVariance b W) = 1 := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  unfold diagonalEntryVariance bondEntryVariance diagonalWeight
  field_simp
  ring

/-- An ordinary derivative in a real
Gaussian coordinate. In particular there is no factor `1/2` in this convention.
This definition fixes notation only and asserts neither differentiability nor IBP. -/
noncomputable def ordinaryRealDerivative (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x

/-- Ordinary real partial derivative in the real coordinate of
`z = x + iy`, holding the imaginary coordinate fixed. -/
noncomputable def complexPartialX (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun x : ℝ => f ⟨x, z.im⟩) z.re

/-- Ordinary real partial derivative in the imaginary coordinate
of `z = x + iy`, holding the real coordinate fixed. -/
noncomputable def complexPartialY (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun y : ℝ => f ⟨z.re, y⟩) z.im

/-- The convention
`∂_Z = (∂_x - i ∂_y)/2`. This is not a complex Fréchet derivative claim. -/
noncomputable def wirtingerZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (complexPartialX f z - Complex.I * complexPartialY f z) / 2

/-- The convention
`∂_{\bar Z} = (∂_x + i ∂_y)/2`. The plus sign is the one paired with `Z`
in the circular Gaussian integration-by-parts formula. -/
noncomputable def wirtingerBarZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (complexPartialX f z + Complex.I * complexPartialY f z) / 2

private theorem hasDerivAt_complexMkX (z : ℂ) :
    HasDerivAt (fun x : ℝ => (⟨x, z.im⟩ : ℂ)) 1 z.re := by
  have h : HasDerivAt (fun x : ℝ => (x : ℂ) + z.im * Complex.I) 1 z.re := by
    convert (hasDerivAt_id z.re).ofReal_comp.add_const (z.im * Complex.I) using 1
    simp
  have hfun : (fun x : ℝ => (⟨x, z.im⟩ : ℂ)) =
      (fun x : ℝ => (x : ℂ) + z.im * Complex.I) := by
    funext x
    apply Complex.ext
    · simp
    · simp
  rw [hfun]
  exact h

private theorem hasDerivAt_complexMkY (z : ℂ) :
    HasDerivAt (fun y : ℝ => (⟨z.re, y⟩ : ℂ)) Complex.I z.im := by
  have h : HasDerivAt (fun y : ℝ => (z.re : ℂ) + y * Complex.I) Complex.I z.im := by
    have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.im :=
      (hasDerivAt_id z.im).ofReal_comp
    convert (hy.mul_const Complex.I).const_add (z.re : ℂ) using 1
    simp
  have hfun : (fun y : ℝ => (⟨z.re, y⟩ : ℂ)) =
      (fun y : ℝ => (z.re : ℂ) + y * Complex.I) := by
    funext y
    apply Complex.ext
    · simp
    · simp
  rw [hfun]
  exact h

private theorem hasDerivAt_star_complexMkX (z : ℂ) :
    HasDerivAt (fun x : ℝ => star (⟨x, z.im⟩ : ℂ)) 1 z.re := by
  have h : HasDerivAt (fun x : ℝ => (x : ℂ) - z.im * Complex.I) 1 z.re := by
    convert (hasDerivAt_id z.re).ofReal_comp.sub_const (z.im * Complex.I) using 1
    simp
  have hfun : (fun x : ℝ => star (⟨x, z.im⟩ : ℂ)) =
      (fun x : ℝ => (x : ℂ) - z.im * Complex.I) := by
    funext x
    apply Complex.ext
    · simp
    · simp
  rw [hfun]
  exact h

private theorem hasDerivAt_star_complexMkY (z : ℂ) :
    HasDerivAt (fun y : ℝ => star (⟨z.re, y⟩ : ℂ)) (-Complex.I) z.im := by
  have h : HasDerivAt (fun y : ℝ => (z.re : ℂ) - y * Complex.I) (-Complex.I) z.im := by
    have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.im :=
      (hasDerivAt_id z.im).ofReal_comp
    convert (hy.mul_const Complex.I).const_sub (z.re : ℂ) using 1
    simp
  have hfun : (fun y : ℝ => star (⟨z.re, y⟩ : ℂ)) =
      (fun y : ℝ => (z.re : ℂ) - y * Complex.I) := by
    funext y
    apply Complex.ext
    · simp
    · simp
  rw [hfun]
  exact h

/-- The implemented `x` partial sends the coordinate function
`z ↦ z` to one. This checks which coordinate is varied, not just later ring algebra. -/
theorem complexPartialX_id (z : ℂ) : complexPartialX (fun w => w) z = 1 :=
  (hasDerivAt_complexMkX z).deriv

/-- The implemented `y` partial sends `z ↦ z` to `i`. -/
theorem complexPartialY_id (z : ℂ) : complexPartialY (fun w => w) z = Complex.I :=
  (hasDerivAt_complexMkY z).deriv

/-- Conjugation has `x` partial one. -/
theorem complexPartialX_star (z : ℂ) :
    complexPartialX (fun w => star w) z = 1 :=
  (hasDerivAt_star_complexMkX z).deriv

/-- Conjugation has `y` partial `-i`, detecting the sign. -/
theorem complexPartialY_star (z : ℂ) :
    complexPartialY (fun w => star w) z = -Complex.I :=
  (hasDerivAt_star_complexMkY z).deriv

/-- The `x` partial of `z * conj z` is `2 Re z`. -/
theorem complexPartialX_mul_star (z : ℂ) :
    complexPartialX (fun w => w * star w) z = 2 * z.re := by
  unfold complexPartialX
  have h := (hasDerivAt_complexMkX z).mul (hasDerivAt_star_complexMkX z)
  convert h.deriv using 1
  apply Complex.ext
  · simp
    ring
  · simp

/-- The `y` partial of `z * conj z` is `2 Im z`. -/
theorem complexPartialY_mul_star (z : ℂ) :
    complexPartialY (fun w => w * star w) z = 2 * z.im := by
  unfold complexPartialY
  have h := (hasDerivAt_complexMkY z).mul (hasDerivAt_star_complexMkY z)
  convert h.deriv using 1
  apply Complex.ext
  · simp
    ring
  · simp

/-- The concrete source convention gives `∂_Z z = 1`. -/
theorem wirtingerZ_id (z : ℂ) : wirtingerZ (fun w => w) z = 1 := by
  simp [wirtingerZ, complexPartialX_id, complexPartialY_id, Complex.I_mul_I]

/-- The concrete source convention gives `∂_{\bar Z} z = 0`. -/
theorem wirtingerBarZ_id (z : ℂ) : wirtingerBarZ (fun w => w) z = 0 := by
  simp [wirtingerBarZ, complexPartialX_id, complexPartialY_id, Complex.I_mul_I]

/-- The concrete source convention gives `∂_Z (conj z) = 0`. -/
theorem wirtingerZ_star (z : ℂ) : wirtingerZ (fun w => star w) z = 0 := by
  rw [wirtingerZ, complexPartialX_star, complexPartialY_star]
  simp [Complex.I_mul_I]

/-- The concrete source convention gives `∂_{\bar Z} (conj z) = 1`. -/
theorem wirtingerBarZ_star (z : ℂ) : wirtingerBarZ (fun w => star w) z = 1 := by
  rw [wirtingerBarZ, complexPartialX_star, complexPartialY_star]
  simp [Complex.I_mul_I]

/-- With these conventions, `∂_Z (z * conj z) = conj z`. -/
theorem wirtingerZ_mul_star (z : ℂ) :
    wirtingerZ (fun w => w * star w) z = star z := by
  rw [wirtingerZ, complexPartialX_mul_star, complexPartialY_mul_star]
  apply Complex.ext
  · simp
  · simp
    ring

/-- With these conventions, `∂_{\bar Z} (z * conj z) = z`. -/
theorem wirtingerBarZ_mul_star (z : ℂ) :
    wirtingerBarZ (fun w => w * star w) z = z := by
  rw [wirtingerBarZ, complexPartialX_mul_star, complexPartialY_mul_star]
  apply Complex.ext
  · simp
  · simp

/-- The factor `1/2` makes the two Wirtinger derivatives recover `∂_x` by addition. -/
theorem wirtingerZ_add_wirtingerBarZ (f : ℂ → ℂ) (z : ℂ) :
    wirtingerZ f z + wirtingerBarZ f z = complexPartialX f z := by
  simp only [wirtingerZ, wirtingerBarZ]
  ring

/-- The sign convention makes `∂_{\bar Z} - ∂_Z = i ∂_y`. -/
theorem wirtingerBarZ_sub_wirtingerZ (f : ℂ → ℂ) (z : ℂ) :
    wirtingerBarZ f z - wirtingerZ f z = Complex.I * complexPartialY f z := by
  simp only [wirtingerZ, wirtingerBarZ]
  ring

/-- The tail event
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
The probability law may depend on every displayed parameter. Public domination
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
No nonnegativity hypothesis is imposed. -/
noncomputable def StochasticDominationConvention {κ ι Ω : Type*} [MeasurableSpace Ω]
    (μ : κ → ι → ℕ → ProbabilityMeasure Ω)
    (X Y : κ → ι → ℕ → Ω → ℝ) (fixed : κ) : Prop :=
  (∀ i N, Measurable (X fixed i N) ∧ Measurable (Y fixed i N)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ i : ι,
        dominationTailProbability μ X Y fixed ε i N ≤
          ENNReal.ofReal (Real.rpow (N : ℝ) (-D))

/-- Stochastic domination includes measurability of both random variables
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

/-- A fixed energy is strictly between the semicircle edges.
This condition excludes endpoints; no uniform compact-bulk margin is asserted. -/
def IsBulkEnergy (E : ℝ) : Prop := -2 < E ∧ E < 2

/-- Exact semicircle density formula, with real `π` and square
root. This definition alone makes no expected-density or intensity assertion. -/
noncomputable def semicircleDensity (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / (2 * Real.pi)

/-- The semicircle square-root argument is positive in the open bulk. -/
theorem semicircleRadicand_pos {E : ℝ} (hE : IsBulkEnergy E) : 0 < 4 - E ^ 2 := by
  have hprod : 0 < (2 - E) * (2 + E) := mul_pos (by linarith [hE.2]) (by linarith [hE.1])
  nlinarith

/-- Fixed open-bulk energy has positive density. -/
theorem semicircleDensity_pos {E : ℝ} (hE : IsBulkEnergy E) :
    0 < semicircleDensity E :=
  div_pos (Real.sqrt_pos.2 (semicircleRadicand_pos hE)) (mul_pos (by norm_num) Real.pi_pos)

/-- Density is even in energy, with no choice of branch/sign. -/
theorem semicircleDensity_neg (E : ℝ) : semicircleDensity (-E) = semicircleDensity E := by
  simp [semicircleDensity]

/-- The exact semicircle formula vanishes at the upper edge. -/
theorem semicircleDensity_two : semicircleDensity 2 = 0 := by
  norm_num [semicircleDensity]

/-- The exact semicircle formula vanishes at the lower edge. -/
theorem semicircleDensity_neg_two : semicircleDensity (-2) = 0 := by
  rw [semicircleDensity_neg, semicircleDensity_two]

/-- Unfolding slope is `Lρ(E)`, not width times density. -/
noncomputable def unfoldingScale (L : ℕ) (E : ℝ) : ℝ :=
  (L : ℝ) * semicircleDensity E

/-- Positive matrix dimension and fixed open-bulk energy give a
positive unfolding slope, independently of every Gaussian-law input. -/
theorem unfoldingScale_pos {L : ℕ} (hL : 0 < L) {E : ℝ} (hE : IsBulkEnergy E) :
    0 < unfoldingScale L E :=
  mul_pos (by exact_mod_cast hL) (semicircleDensity_pos hE)

/-- Map a physical eigenvalue `λ` to `Lρ(E)(λ-E)`. -/
noncomputable def unfoldEigenvalue (L : ℕ) (E lam : ℝ) : ℝ :=
  unfoldingScale L E * (lam - E)

/-- The physical coordinate `e(u)`: the inverse affine map `E + u/(Lρ(E))`. -/
noncomputable def physicalEnergy (L : ℕ) (E u : ℝ) : ℝ :=
  E + u / unfoldingScale L E

/-- The chosen central energy maps exactly to zero. -/
theorem unfoldEigenvalue_center (L : ℕ) (E : ℝ) : unfoldEigenvalue L E E = 0 := by
  simp [unfoldEigenvalue]

/-- Inversion from an unfolded coordinate requires both positive
dimension and bulk energy; the zero-density endpoints are deliberately excluded. -/
theorem unfoldEigenvalue_physicalEnergy {L : ℕ} (hL : 0 < L) {E : ℝ}
    (hE : IsBulkEnergy E) (u : ℝ) :
    unfoldEigenvalue L E (physicalEnergy L E u) = u := by
  have hs : unfoldingScale L E ≠ 0 := ne_of_gt (unfoldingScale_pos hL hE)
  simp only [unfoldEigenvalue, physicalEnergy, add_sub_cancel_left]
  exact mul_div_cancel₀ u hs

/-- Every physical spectral location is recovered by the inverse
map at fixed finite positive dimension and fixed open-bulk energy. -/
theorem physicalEnergy_unfoldEigenvalue {L : ℕ} (hL : 0 < L) {E : ℝ}
    (hE : IsBulkEnergy E) (lam : ℝ) :
    physicalEnergy L E (unfoldEigenvalue L E lam) = lam := by
  have hs : unfoldingScale L E ≠ 0 := ne_of_gt (unfoldingScale_pos hL hE)
  simp [unfoldEigenvalue, physicalEnergy, hs]

/-- Positive rescaling preserves strict spectral ordering. -/
theorem unfoldEigenvalue_strictMono {L : ℕ} (hL : 0 < L) {E : ℝ}
    (hE : IsBulkEnergy E) : StrictMono (unfoldEigenvalue L E) := by
  intro x y hxy
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hxy E) (unfoldingScale_pos hL hE)

/-- Distinct physical spectral locations remain distinct after
rescaling; this does not prove that a random matrix's spectrum is simple. -/
theorem unfoldEigenvalue_injective {L : ℕ} (hL : 0 < L) {E : ℝ}
    (hE : IsBulkEnergy E) : Function.Injective (unfoldEigenvalue L E) :=
  (unfoldEigenvalue_strictMono hL hE).injective

end CoareaNative.BlockBand.Conventions
