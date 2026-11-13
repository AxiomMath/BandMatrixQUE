module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.TikhonovAlg
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegAlg
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The regularized drivers have identity bracket

* `bil_zDens`: the bilinear form of the joint density `zDens s = diag(s sᵀ, I)`.
* **`bil_hval`**: for `ε > 0`, `hval s ε · zDens s · hval s εᵀ = I` (the rows of `tikX s ε`
  are orthonormal, `tikX_orth`).
* **`bil_offval`**: `offval · zDens 0 · offvalᵀ = I`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix
open BlockBand.SourceProcess.Stochastic.Representation

variable {d : ℕ}

theorem bil_zDens (s : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d ⊕ Fin (d + d) → ℝ) :
    ∑ c, ∑ c', u c * v c' * zDens s c c' =
      ∑ m, (∑ i, u (Sum.inl i) * s i m) * (∑ j, v (Sum.inl j) * s j m) +
        ∑ l, u (Sum.inr l) * v (Sum.inr l) := by
  simp only [Fintype.sum_sum_type, zDens, Sum.elim_inl, Sum.elim_inr, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  have e1 : ∀ m, (∑ i, u (Sum.inl i) * s i m) * (∑ j, v (Sum.inl j) * s j m) =
      ∑ i, ∑ j, u (Sum.inl i) * s i m * (v (Sum.inl j) * s j m) := fun m => by
    rw [Finset.sum_mul_sum]
  have key : ∀ i j, u (Sum.inl i) * v (Sum.inl j) * (s * sᵀ) i j =
      ∑ m, u (Sum.inl i) * s i m * (v (Sum.inl j) * s j m) := fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.transpose_apply]; ring
  simp only [e1, key]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- **The regularized driver integrand has identity bracket.** -/
theorem bil_hval (s : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Fin d) :
    ∑ c, ∑ c', hval s ε k c * hval s ε l c' * zDens s c c' = if k = l then 1 else 0 := by
  rw [bil_zDens, ← tikX_orth s hε k l, Fintype.sum_sum_type]
  have e1 : ∀ k m, ∑ i, hval s ε k (Sum.inl i) * s i m = tikX s ε k (Sum.inl m) := fun k m => by
    simp [hval, tikX, Matrix.mul_apply]
  simp only [e1]
  rfl

/-- **The driver integrand after the stopping time has identity bracket.** -/
theorem bil_offval (k l : Fin d) :
    ∑ c, ∑ c', offval k c * offval l c' * zDens 0 c c' = if k = l then 1 else 0 := by
  rw [bil_zDens]
  simp only [offval, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, mul_zero,
    zero_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (Fin.castAdd d l)]
  simp [Fin.castAdd_inj, eq_comm]

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
