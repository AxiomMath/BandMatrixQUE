module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Star.Real

/-!
# Gram determinants with unit diagonal

A Gram matrix `Bᵀ B` with unit diagonal has determinant in `[0, 1]`: its eigenvalues are
nonnegative with sum `k`, and `x ≤ e^{x-1}` (`gram_det_nonneg_and_le_one`). Consequently a kernel
`K x y = ∑ i, ψ i x * ψ i y` over a finite index type with `K x x = 1` has all Gram determinants
in `[0, 1]` (`kernel_det_nonneg_and_le_one`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix

/-- For a finite index type `ι'`, `k : ℕ` and a real matrix
`B : Matrix ι' (Fin k) ℝ` whose Gram matrix `Bᵀ * B` has all diagonal entries
equal to `1`, the Gram determinant satisfies `0 ≤ det (Bᵀ * B) ≤ 1`. -/
theorem gram_det_nonneg_and_le_one {ι' : Type*} [Fintype ι'] {k : ℕ}
    (B : Matrix ι' (Fin k) ℝ) (hdiag : ∀ a, (Bᵀ * B) a a = 1) :
    0 ≤ (Bᵀ * B).det ∧ (Bᵀ * B).det ≤ 1 := by
  have hP : (Bᵀ * B).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self B
  refine ⟨hP.det_nonneg, ?_⟩
  have hH := hP.isHermitian
  have hdet : (Bᵀ * B).det = ∏ a, hH.eigenvalues a := by
    simpa using hH.det_eq_prod_eigenvalues
  have htr : (Bᵀ * B).trace = ∑ a, hH.eigenvalues a := by
    simpa using hH.trace_eq_sum_eigenvalues
  have htr' : (Bᵀ * B).trace = k := by
    simp [Matrix.trace, hdiag]
  rw [hdet]
  calc ∏ a, hH.eigenvalues a ≤ ∏ a, Real.exp (hH.eigenvalues a - 1) := by
        refine Finset.prod_le_prod₀ (fun a _ => hP.eigenvalues_nonneg a) (fun a _ => ?_)
        linarith [Real.add_one_le_exp (hH.eigenvalues a - 1)]
    _ = Real.exp (∑ a, (hH.eigenvalues a - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by
        rw [Finset.sum_sub_distrib, ← htr, htr']
        simp

/-- Kernel form of the Gram bound. Let `ι` be a finite type,
`ψ : ι → ℝ → ℝ` arbitrary, and `K x y = ∑ i, ψ i x * ψ i y` with `K x x = 1`
for every `x : ℝ`. Then for every `k : ℕ` and every configuration
`y : Fin k → ℝ`, `0 ≤ det [K (y a) (y b)] ≤ 1`. -/
theorem kernel_det_nonneg_and_le_one {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (hdiag : ∀ x, K x x = 1) (k : ℕ) (y : Fin k → ℝ) :
    0 ≤ Matrix.det (fun a b : Fin k => K (y a) (y b)) ∧
      Matrix.det (fun a b : Fin k => K (y a) (y b)) ≤ 1 := by
  let B : Matrix ι (Fin k) ℝ := Matrix.of fun i a => ψ i (y a)
  have hB : (fun a b : Fin k => K (y a) (y b)) = Bᵀ * B := by
    ext a b
    simp [B, Matrix.mul_apply, hK]
  rw [hB]
  refine gram_det_nonneg_and_le_one B fun a => ?_
  rw [← hB]
  exact hdiag (y a)

/-- Absolute-value form of `kernel_det_nonneg_and_le_one`: under the same
hypotheses (`K x y = ∑ i, ψ i x * ψ i y` over a finite `ι`, `K x x = 1` for
all `x : ℝ`), every `k : ℕ` and `y : Fin k → ℝ` satisfy
`|det [K (y a) (y b)]| ≤ 1`. -/
theorem abs_kernel_det_le_one {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (hdiag : ∀ x, K x x = 1) (k : ℕ) (y : Fin k → ℝ) :
    |Matrix.det (fun a b : Fin k => K (y a) (y b))| ≤ 1 := by
  obtain ⟨h0, h1⟩ := kernel_det_nonneg_and_le_one ψ K hK hdiag k y
  rw [abs_of_nonneg h0]
  exact h1

end BlockBand.Endpoints
