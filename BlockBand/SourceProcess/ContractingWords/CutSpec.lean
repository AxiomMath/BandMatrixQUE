module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Spectral cuts at a Hermitian letter

Deterministic identities expanding bilinear forms and traces through the spectral decomposition of
a Hermitian matrix.

* `bilinear_mul_herm_mul`: `u*(P A Q)v = Σ_m λ_m (u*P e_m)(e_m* Q v)`;
* `trace_herm_mul`: `Tr(A M) = Σ_m λ_m e_m* M e_m`;
* `nuclearNorm_eq_sum`: `Tr|A| = Σ_m |λ_m|`; `vecNorm_eigVec`: `‖e_m‖ = 1`.
This is the singular-value cut of the paper, made at a Hermitian letter (`J` or `Q_a`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The `m`-th eigenvector of a Hermitian matrix, as a column of `eigenvectorUnitary`. -/
def eigVec {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : n) : n → ℂ :=
  fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i m

theorem herm_eq_udu {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun m => ((hA.eigenvalues m : ℝ) : ℂ)) * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

omit [DecidableEq n] in
theorem bilinear_eq_vecMul (u : n → ℂ) (M : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u M v = (star u ᵥ* M) ⬝ᵥ v := by
  rw [bilinear, dotProduct_mulVec]

theorem bilinear_udu (U : Matrix n n ℂ) (d : n → ℂ) (P Q : Matrix n n ℂ) (u v : n → ℂ) :
    bilinear u (P * (U * diagonal d * star U) * Q) v =
      ∑ m, d m * bilinear u P (fun i => U i m) * bilinear (fun i => U i m) Q v := by
  have e : P * (U * diagonal d * star U) * Q = (P * U) * diagonal d * (star U * Q) := by
    simp only [Matrix.mul_assoc]
  rw [e, bilinear_eq_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul]
  simp only [dotProduct, vecMul_diagonal]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (star u ᵥ* (P * U)) m = bilinear u P (fun i => U i m) := by
    rw [bilinear_eq_vecMul, ← vecMul_vecMul]; rfl
  have h2 : ((star U * Q) *ᵥ v) m = bilinear (fun i => U i m) Q v := by
    rw [← mulVec_mulVec]
    simp only [bilinear, mulVec, dotProduct, star_eq_conjTranspose, conjTranspose_apply,
      Pi.star_apply]
  rw [h1, h2]; ring

theorem trace_udu (U : Matrix n n ℂ) (d : n → ℂ) (M : Matrix n n ℂ) :
    ((U * diagonal d * star U) * M).trace =
      ∑ m, d m * bilinear (fun i => U i m) M (fun i => U i m) := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc M,
    ← Matrix.mul_assoc]
  simp only [trace, diag, mul_diagonal]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]
  congr 1

/-- **The cut at a Hermitian letter**: `u*(PAQ)v = Σ_m λ_m (u*Pe_m)(e_m*Qv)`. -/
theorem bilinear_mul_herm_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (P Q : Matrix n n ℂ)
    (u v : n → ℂ) :
    bilinear u (P * A * Q) v =
      ∑ m, ((hA.eigenvalues m : ℝ) : ℂ) * bilinear u P (eigVec hA m) *
        bilinear (eigVec hA m) Q v := by
  have h := herm_eq_udu hA
  calc bilinear u (P * A * Q) v = bilinear u (P * ((hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun m => ((hA.eigenvalues m : ℝ) : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix n n ℂ)) * Q) v := by
        exact congrArg (fun B => bilinear u (P * B * Q) v) h
    _ = _ := bilinear_udu _ _ P Q u v

/-- `Tr(AM) = Σ_m λ_m e_m* M e_m`. -/
theorem trace_herm_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (M : Matrix n n ℂ) :
    (A * M).trace = ∑ m, ((hA.eigenvalues m : ℝ) : ℂ) * bilinear (eigVec hA m) M (eigVec hA m) := by
  have h := herm_eq_udu hA
  calc (A * M).trace = (((hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun m => ((hA.eigenvalues m : ℝ) : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix n n ℂ)) * M).trace := by
        exact congrArg (fun B => (B * M).trace) h
    _ = _ := trace_udu _ _ M

/-- `Tr|A| = Σ_m |λ_m|` for Hermitian `A`. -/
theorem nuclearNorm_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    nuclearNorm A = ∑ m, |hA.eigenvalues m| := by
  rw [nuclearNorm, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  rw [Finset.sum]
  congr 1
  refine Multiset.map_congr rfl fun m _ => ?_
  simp

theorem nuclearNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ nuclearNorm A :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_nonneg z

theorem vecNorm_eigVec {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : n) :
    vecNorm (eigVec hA m) = 1 := by
  set U : Matrix n n ℂ := ↑hA.eigenvectorUnitary with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h := congrFun (congrFun hU m) m
  simp only [Matrix.mul_apply, star_apply, one_apply_eq] at h
  have h2 : ∑ i, ‖U i m‖ ^ 2 = 1 := by
    have : ((∑ i, ‖U i m‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.mul_conj', mul_comm]; rfl
    exact_mod_cast this
  rw [vecNorm]
  simp only [eigVec, ← hUdef, h2, Real.sqrt_one]

end BlockBand.SourceProcess.ContractingWords
