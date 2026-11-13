module

public import BlockBand.Window.Count.SpectralSmoothing

/-!
# Spectral calculus of Hermitian matrices for the trace gradient

*Conventions.* For a Hermitian `A` with eigenvector unitary `U` and eigenvalues `λ_j`,
`hA.cfc g = U diag(g(λ)) U*` is Mathlib's spectral functional calculus
(`Matrix.IsHermitian.cfc`, equal to the generic `cfc` by `Matrix.IsHermitian.cfc_eq`).
`fcalc g M` is `hM.cfc g` for Hermitian `M` and `0` otherwise.

## Main results

* `trace_cfc_mul`: `Tr(g(A) K) = Σ_j g(λ_j) (U* K U)_jj`.
* `abs_re_trace_cfc_mul_le`: `|Re Tr(g(A) K)| ≤ (Σ_j |g(λ_j)|) Σ_{a,b} ‖K_ab‖`.
* `abs_eigenvalues_le`: `|λ_j(A)| ≤ Σ_{a,b} ‖A_ab‖`.
* `re_trace_cfc`: `Re Tr g(A) = Σ_j g(λ_j)`; `cfc_mul_cfc`, `cfc_sub'`, `isHermitian_cfc`,
  `cfc_eval_eq_aeval` (polynomials).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count.SpectralCalculus

open Matrix
open scoped ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `U* K U` diagonal entries are bounded by the entrywise `ℓ¹` norm of `K`. -/
theorem norm_star_mul_mul_diag_le (U : Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) (j : n) :
    ‖(star (U : Matrix n n ℂ) * K * U) j j‖ ≤ ∑ a, ∑ b, ‖K a b‖ := by
  have hU := U.2
  have e : (star (U : Matrix n n ℂ) * K * U) j j =
      ∑ a, ∑ b, star ((U : Matrix n n ℂ) a j) * K a b * (U : Matrix n n ℂ) b j := by
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have h1 := entry_norm_bound_of_unitary hU a j
  have h2 := entry_norm_bound_of_unitary hU b j
  have h3 := norm_nonneg (K a b)
  calc ‖(U : Matrix n n ℂ) a j‖ * ‖K a b‖ * ‖(U : Matrix n n ℂ) b j‖
      ≤ 1 * ‖K a b‖ * 1 := by gcongr
    _ = ‖K a b‖ := by ring

variable {A : Matrix n n ℂ} (hA : A.IsHermitian)

include hA in
theorem cfc_def (g : ℝ → ℝ) :
    hA.cfc g = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun j => ((g (hA.eigenvalues j) : ℝ) : ℂ)) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

include hA in
theorem star_mul_self_mul_diag :
    star (hA.eigenvectorUnitary : Matrix n n ℂ) * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  exact h

include hA in
/-- `Tr(g(A) K) = Σ_j g(λ_j) (U* K U)_jj`. -/
theorem trace_cfc_mul (g : ℝ → ℝ) (K : Matrix n n ℂ) :
    trace (hA.cfc g * K) = ∑ j, ((g (hA.eigenvalues j) : ℝ) : ℂ) *
      (star (hA.eigenvectorUnitary : Matrix n n ℂ) * K * (hA.eigenvectorUnitary : Matrix n n ℂ)) j j := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (fun j => ((g (hA.eigenvalues j) : ℝ) : ℂ))
  rw [cfc_def hA g]
  change trace (U * D * star U * K) = _
  have : U * D * star U * K = U * (D * (star U * K)) := by simp only [Matrix.mul_assoc]
  rw [this, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [show D * (star U * (K * U)) = D * (star U * K * U) by simp only [Matrix.mul_assoc]]
  simp only [trace, diag, D, diagonal_mul, Matrix.mul_assoc]

include hA in
/-- `|Re Tr(g(A) K)| ≤ (Σ_j |g(λ_j)|) Σ_{a,b} ‖K_ab‖`. -/
theorem abs_re_trace_cfc_mul_le (g : ℝ → ℝ) (K : Matrix n n ℂ) :
    |(trace (hA.cfc g * K)).re| ≤ (∑ j, |g (hA.eigenvalues j)|) * ∑ a, ∑ b, ‖K a b‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [trace_cfc_mul hA g K, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_star_mul_mul_diag_le _ K j) (abs_nonneg _)

include hA in
/-- `|λ_j(A)| ≤ Σ_{a,b} ‖A_ab‖`. -/
theorem abs_eigenvalues_le (j : n) : |hA.eigenvalues j| ≤ ∑ a, ∑ b, ‖A a b‖ := by
  have h := norm_star_mul_mul_diag_le hA.eigenvectorUnitary A j
  rw [star_mul_self_mul_diag hA, diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

include hA in
theorem trace_cfc (g : ℝ → ℝ) : trace (hA.cfc g) = ∑ j, ((g (hA.eigenvalues j) : ℝ) : ℂ) := by
  have h := trace_cfc_mul hA g 1
  rw [Matrix.mul_one, Matrix.mul_one] at h
  rw [h]
  have hU : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  simp [hU]

include hA in
theorem re_trace_cfc (g : ℝ → ℝ) : (trace (hA.cfc g)).re = ∑ j, g (hA.eigenvalues j) := by
  rw [trace_cfc hA g, Complex.re_sum]
  simp

include hA in
theorem cfc_mul_cfc (g h : ℝ → ℝ) : hA.cfc g * hA.cfc h = hA.cfc (fun y => g y * h y) := by
  simp only [IsHermitian.cfc]
  rw [← map_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  simp

include hA in
theorem cfc_sub' (g h : ℝ → ℝ) : hA.cfc (fun y => g y - h y) = hA.cfc g - hA.cfc h := by
  simp only [IsHermitian.cfc]
  rw [← map_sub, diagonal_sub]
  congr 2
  funext j
  simp

include hA in
theorem isHermitian_cfc (g : ℝ → ℝ) : (hA.cfc g).IsHermitian := by
  rw [← IsHermitian.cfc_eq hA g]
  exact cfc_predicate g A

include hA in
theorem cfc_eval_eq_aeval (p : Polynomial ℝ) : hA.cfc (fun y => p.eval y) = Polynomial.aeval A p := by
  rw [← IsHermitian.cfc_eq hA]
  exact cfc_polynomial p A hA.isSelfAdjoint

/-- Spectral functional calculus, `0` off the Hermitian matrices. -/
def fcalc (g : ℝ → ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ := by
  classical
  exact if h : M.IsHermitian then h.cfc g else 0

include hA in
theorem fcalc_eq (g : ℝ → ℝ) : fcalc g A = hA.cfc g := by
  unfold fcalc
  simp only [hA, ↓reduceDIte]

include hA in
theorem spectralSum_eq (g : ℝ → ℝ) : spectralSum g A = ∑ j, g (hA.eigenvalues j) := by
  unfold spectralSum
  simp only [hA, ↓reduceDIte]

include hA in
theorem spectralSum_eq_re_trace (g : ℝ → ℝ) : spectralSum g A = (trace (fcalc g A)).re := by
  rw [spectralSum_eq hA, fcalc_eq hA, re_trace_cfc hA]

end BlockBand.Window.Count.SpectralCalculus
