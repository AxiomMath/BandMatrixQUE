module

public import Mathlib

/-!
# The entire law: a determinant bound for tightness

`norm_det_one_add_le`: for every complex square matrix `B`,
`|det(I + B)| ≤ exp{Re Tr B + ½‖B‖²_HS}`. This bound is used for the growth of the finite
determinants in the tightness step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- `Tr(B^*B) = ‖B‖²_HS`. -/
theorem trace_conjTranspose_mul_self_eq {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) :
    (Bᴴ * B).trace = ((∑ i, ∑ j, ‖B i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', RCLike.star_def]

/-- **Determinant bound**: `|det(I + B)| ≤ exp{Re Tr B + ½‖B‖²_HS}` for every
complex square matrix `B`. Proof: `|det(I+B)|² = det M`, `M = (I+B)^*(I+B) ⪰ 0`, and
`det M = Π μ_k ≤ Π e^{μ_k - 1} = exp(Tr M - d)`, `Tr M - d = 2 Re Tr B + ‖B‖²_HS`. -/
theorem norm_det_one_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    ‖(1 + B).det‖ ≤ Real.exp ((B.trace).re + 2⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  set M : Matrix ι ι ℂ := (1 + B)ᴴ * (1 + B)
  have hM : M.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self (1 + B)
  have hH : M.IsHermitian := hM.isHermitian
  set μ := hH.eigenvalues
  have hμ : ∀ k, 0 ≤ μ k := fun k => hM.eigenvalues_nonneg k
  have hdet : ((‖(1 + B).det‖ ^ 2 : ℝ) : ℂ) = ∏ k, (μ k : ℂ) := by
    have h2 : M.det = ∏ k, (μ k : ℂ) := by rw [hH.det_eq_prod_eigenvalues]; rfl
    rw [← h2]
    simp only [M, Matrix.det_mul, Matrix.det_conjTranspose]
    rw [RCLike.star_def, Complex.conj_mul']
    push_cast; rfl
  have hdetR : ‖(1 + B).det‖ ^ 2 = ∏ k, μ k := by
    exact_mod_cast hdet
  have htr : ((∑ k, μ k : ℝ) : ℂ) = M.trace := by
    rw [hH.trace_eq_sum_eigenvalues]; push_cast; rfl
  have htrM : M.trace = (Fintype.card ι : ℂ) + B.trace + star B.trace +
      ((∑ i, ∑ j, ‖B i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [M, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_one,
      Matrix.trace_conjTranspose, trace_conjTranspose_mul_self_eq]
    ring
  have hsum : ∑ k, μ k = Fintype.card ι + 2 * (B.trace).re + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
    have h := congrArg Complex.re (htr.trans htrM)
    simp only [Complex.ofReal_re, Complex.add_re, Complex.natCast_re, RCLike.star_def,
      Complex.conj_re] at h
    linarith
  have hprod : ∏ k, μ k ≤ Real.exp (∑ k, (μ k - 1)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun k _ => hμ k) fun k _ => ?_
    have := Real.add_one_le_exp (μ k - 1)
    linarith
  have hsq : ‖(1 + B).det‖ ^ 2 ≤
      Real.exp ((B.trace).re + 2⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2) ^ 2 := by
    rw [hdetR, ← Real.exp_nat_mul]
    refine hprod.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
    rw [Finset.sum_sub_distrib, hsum]
    simp
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp hsq

end BlockBand.Critical.EntireLaw
