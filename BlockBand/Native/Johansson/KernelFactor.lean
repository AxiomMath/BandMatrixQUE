module

public import BlockBand.Native.Johansson.Biorthogonal
public import BlockBand.DeterminantScore.WeylIntegrationInterlace

/-!
# Johansson's formula (2.18): factorization of the kernel determinant

* `gaussDetScaling_holds : GaussDetScalingStatement`,
  `det[p_S(x_i - d_j)] = (2πS)^{-N/2} e^{-(Σx² + Σd²)/(2S)} E(x, d/S)`
  (row and column factors pulled out of the determinant);
* `kernelFactor_holds : KernelFactorStatement`, `det[K(x_i, x_l)] = Δ(x)/Δ(d) · det[p_S(x_i - d_j)]`
  for every `x`.

Proof of the factorization: `[K(x_i, x_l)] = [p_S(x_i - d_j)] · [q_j(x_l)]`; `T` is linear on
polynomials of degree `< N`, so `[q_j(x_l)] = L · W(x)` with `L` the Lagrange coefficient matrix
and `W(x)_{pl} = (T X^p)(x_l)`; `W(x) = U · V(x)ᵀ` with `U` lower unitriangular (`T X^p = X^p` +
lower order), so `det W(x) = Δ(x)`; and `L · V(d)ᵀ = I` (`Lagrange.eval_basis_self`), so
`det L = 1/Δ(d)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal NNReal BigOperators

/-!
## Gaussian scaling of the determinant `det[p_S(x_i - d_j)]`
-/

/-- **`GaussDetScalingStatement`**. -/
theorem gaussDetScaling_holds : GaussDetScalingStatement := by
  intro N S _ d x
  set c := (Real.sqrt (2 * Real.pi * S))⁻¹
  have hM : (Matrix.of fun i j => gaussKernel S (d j) (x i)) =
      Matrix.of fun i j => (c * Real.exp (-(x i ^ 2) / (2 * (S : ℝ)))) *
        (Real.exp (-(d j ^ 2) / (2 * (S : ℝ))) * Real.exp (x i * d j / (S : ℝ))) := by
    ext i j
    simp only [Matrix.of_apply, gaussKernel, gaussianPDFReal, c, mul_assoc]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h1 := Matrix.det_mul_column (fun i => c * Real.exp (-(x i ^ 2) / (2 * (S : ℝ))))
    (Matrix.of fun i j => Real.exp (-(d j ^ 2) / (2 * (S : ℝ))) * Real.exp (x i * d j / (S : ℝ)))
  have h2 := Matrix.det_mul_row (fun j => Real.exp (-(d j ^ 2) / (2 * (S : ℝ))))
    (Matrix.of fun i j => Real.exp (x i * d j / (S : ℝ)))
  simp only [Matrix.of_apply] at h1 h2
  rw [hM, h1, h2, expDet, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, ← Real.exp_sum, mul_assoc, mul_assoc, ← mul_assoc
    (Real.exp _), ← Real.exp_add]
  congr 3
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib, neg_add]

/-!
## Linearity and triangularity of the inverse heat transform
-/

theorem heatInv_eq_sum_range (S : ℝ≥0) (P : ℝ[X]) {M : ℕ} (hM : P.natDegree < M) :
    heatInv S P = ∑ r ∈ Finset.range M,
      Polynomial.C ((-1) ^ r * gaussMoment S (2 * r)) * hasseDeriv (2 * r) P := by
  have hz : ∀ r, P.natDegree < r →
      Polynomial.C ((-1) ^ r * gaussMoment S (2 * r)) * hasseDeriv (2 * r) P = 0 := by
    intro r hr
    rw [hasseDeriv_eq_zero_of_lt_natDegree P _ (by omega), mul_zero]
  unfold heatInv
  rw [Finset.sum_subset (Finset.range_subset_range.2 (Nat.le_add_right _ M))
      (fun r _ hr => hz r (by simp at hr; omega)),
    Finset.sum_subset (Finset.range_subset_range.2 (Nat.le_add_left M (P.natDegree + 1)))
      (fun r _ hr => hz r (by simp at hr; omega))]

theorem heatInv_eq_sum_coeff (S : ℝ≥0) (P : ℝ[X]) {M : ℕ} (hM : P.natDegree < M) :
    heatInv S P = ∑ p ∈ Finset.range M, Polynomial.C (P.coeff p) * heatInv S (X ^ p) := by
  have hX : ∀ p ∈ Finset.range M, heatInv S (X ^ p : ℝ[X]) = ∑ r ∈ Finset.range M,
      Polynomial.C ((-1) ^ r * gaussMoment S (2 * r)) * hasseDeriv (2 * r) (X ^ p) := by
    intro p hp
    exact heatInv_eq_sum_range S _ (by rw [natDegree_X_pow]; simpa using hp)
  rw [Finset.sum_congr rfl fun p hp => by rw [hX p hp], heatInv_eq_sum_range S P hM]
  conv_lhs => rw [as_sum_range_C_mul_X_pow' (p := P) hM]
  simp_rw [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  rw [← smul_eq_C_mul (P.coeff p), map_smul, smul_eq_C_mul]
  ring

theorem coeff_heatInv_X_pow_self (S : ℝ≥0) (p : ℕ) : (heatInv S (X ^ p : ℝ[X])).coeff p = 1 := by
  unfold heatInv
  rw [finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [gaussMoment_zero]
  · intro r _ hr
    rw [coeff_C_mul, hasseDeriv_coeff, coeff_X_pow]
    simp [hr]
  · intro h; simp at h

theorem natDegree_heatInv_X_pow_le (S : ℝ≥0) (p : ℕ) :
    (heatInv S (X ^ p : ℝ[X])).natDegree ≤ p :=
  (natDegree_heatInv_le S _).trans (natDegree_X_pow_le p)

/-!
## Determinants of polynomial evaluation matrices
-/

/-- `det[f_j(x_l)] = det[coeff(f_j, m)] · det V(x)` for polynomials of degree `< N`. -/
theorem det_eval_eq_det_coeff_mul {N : ℕ} (f : Fin N → ℝ[X]) (hf : ∀ j, (f j).natDegree < N)
    (x : Fin N → ℝ) :
    (Matrix.of fun j l => (f j).eval (x l)).det =
      (Matrix.of fun j (m : Fin N) => (f j).coeff m).det * (Matrix.vandermonde x).det := by
  rw [← Matrix.det_transpose (Matrix.vandermonde x), ← Matrix.det_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [eval_eq_sum_range' (hf j), ← Fin.sum_univ_eq_sum_range (fun m => (f j).coeff m * x l ^ m)]

theorem det_heatInv_X_pow_eval {N : ℕ} (S : ℝ≥0) (x : Fin N → ℝ) :
    (Matrix.of fun (p l : Fin N) => (heatInv S (X ^ (p : ℕ) : ℝ[X])).eval (x l)).det =
      (Matrix.vandermonde x).det := by
  rw [det_eval_eq_det_coeff_mul (fun p : Fin N => heatInv S (X ^ (p : ℕ)))
    (fun p => (natDegree_heatInv_X_pow_le S p).trans_lt p.2), Matrix.det_of_isLowerTriangular,
    Finset.prod_eq_one, one_mul]
  · intro p _
    exact coeff_heatInv_X_pow_self S p
  · intro p m hpm
    exact coeff_eq_zero_of_natDegree_lt ((natDegree_heatInv_X_pow_le S p).trans_lt hpm)

theorem det_lagrangeCoeff_mul_det_vandermonde {N : ℕ} (d : Fin N → ℝ) (hd : StrictMono d) :
    (Matrix.of fun j (p : Fin N) => (lagrangeBasis d j).coeff p).det *
      (Matrix.vandermonde d).det = 1 := by
  rw [← det_eval_eq_det_coeff_mul (fun j => lagrangeBasis d j)
    (fun j => (natDegree_lagrangeBasis_le d j).trans_lt (by have := j.2; omega))]
  have h1 : (Matrix.of fun j l => (lagrangeBasis d j).eval (d l)) = 1 := by
    ext j l
    rw [Matrix.of_apply, lagrangeBasis_eval d hd, Matrix.one_apply]
  rw [h1, Matrix.det_one]

theorem biorthPoly_eval_eq_sum {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (j : Fin N) (y : ℝ) :
    (biorthPoly S d j).eval y =
      ∑ p : Fin N, (lagrangeBasis d j).coeff p * (heatInv S (X ^ (p : ℕ) : ℝ[X])).eval y := by
  rw [biorthPoly, heatInv_eq_sum_coeff (M := N) S _
    ((natDegree_lagrangeBasis_le d j).trans_lt (by have := j.2; omega)), eval_finsetSum,
    ← Fin.sum_univ_eq_sum_range (fun p => ((C ((lagrangeBasis d j).coeff p)) *
      heatInv S (X ^ p)).eval y)]
  simp only [eval_mul, eval_C]

theorem det_biorthPoly_eval {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (hd : StrictMono d)
    (x : Fin N → ℝ) :
    (Matrix.of fun j l => (biorthPoly S d j).eval (x l)).det =
      (Matrix.vandermonde x).det / (Matrix.vandermonde d).det := by
  have hB : (Matrix.of fun j l => (biorthPoly S d j).eval (x l)) =
      (Matrix.of fun j (p : Fin N) => (lagrangeBasis d j).coeff p) *
        Matrix.of fun (p l : Fin N) => (heatInv S (X ^ (p : ℕ) : ℝ[X])).eval (x l) := by
    ext j l
    simp only [Matrix.of_apply, Matrix.mul_apply, biorthPoly_eval_eq_sum]
  have hL := det_lagrangeCoeff_mul_det_vandermonde d hd
  have hV : (Matrix.vandermonde d).det ≠ 0 := by
    intro h; rw [h, mul_zero] at hL; exact zero_ne_one hL
  rw [hB, Matrix.det_mul, det_heatInv_X_pow_eval, eq_div_iff hV]
  linear_combination (Matrix.vandermonde x).det * hL

/-!
## The factorization
-/

/-- **`KernelFactorStatement`**: `det[K(x_i, x_l)] = Δ(x)/Δ(d) · det[p_S(x_i - d_j)]`. -/
theorem kernelFactor_holds : KernelFactorStatement := by
  intro N S _ d hd x
  have hK : (Matrix.of fun i l => sourceKernel S d (x i) (x l)) =
      (Matrix.of fun i j => gaussKernel S (d j) (x i)) *
        Matrix.of fun j l => (biorthPoly S d j).eval (x l) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.mul_apply, sourceKernel]
  rw [kernelMatDet, hK, Matrix.det_mul, det_biorthPoly_eval S d hd,
    DeterminantScore.WeylIntegration.vandermonde_eq_det,
    DeterminantScore.WeylIntegration.vandermonde_eq_det, mul_comm]

end BlockBand.Native.Johansson
