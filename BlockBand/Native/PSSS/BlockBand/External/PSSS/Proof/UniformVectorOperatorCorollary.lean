module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorSmallBall
public import Mathlib.Analysis.Matrix.Normed

/-!
# Operator-norm corollary of the uniform-vector small-ball estimate

This module compares the `L²` matrix operator norm with the exact vectorized
Frobenius normalization used by the PSSS uniform-sphere estimate, and derives
the large-image probability statement at the source threshold `1/(10√N)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- Matrix-vector multiplication is bounded by the Euclidean norm of all
matrix entries. -/
theorem norm_mulVec_le_matrixVecNorm_mul {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ (Fin N))‖ ≤
      ‖(WithLp.toLp 2 (Matrix.vec Q) :
        EuclideanSpace ℂ (Fin N × Fin N))‖ * ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
  rw [mul_pow, norm_sq_matrix_vec_eq_sum Q, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  calc
    (∑ i, ‖(Q *ᵥ WithLp.ofLp x) i‖ ^ 2) ≤
        ∑ i, (∑ j, ‖Q i j‖ ^ 2) * (∑ j, ‖WithLp.ofLp x j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
    ‖(Q *ᵥ WithLp.ofLp x) i‖ ^ 2 =
        ‖inner ℂ (WithLp.toLp 2 (star (Q i ·)) : EuclideanSpace ℂ (Fin N)) x‖ ^ 2 := by
            congr 2
            simp [Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
      _ ≤ (‖(WithLp.toLp 2 (star (Q i ·)) : EuclideanSpace ℂ (Fin N))‖ * ‖x‖) ^ 2 :=
        sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr
          (norm_inner_le_norm _ _)
      _ = (∑ j, ‖Q i j‖ ^ 2) * (∑ j, ‖WithLp.ofLp x j‖ ^ 2) := by
        rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq x]
        congr 1
        simp
    _ = (∑ i, ∑ j, ‖Q i j‖ ^ 2) * (∑ j, ‖WithLp.ofLp x j‖ ^ 2) := by
      rw [Finset.sum_mul]

open scoped Matrix.Norms.L2Operator in
/-- The `L²` operator norm is bounded by the Euclidean norm of all matrix
entries.  The left norm is deliberately scoped: no global matrix norm instance
is changed. -/
theorem l2OperatorNorm_le_matrixVecNorm {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    ‖Q‖ ≤ ‖(WithLp.toLp 2 (Matrix.vec Q) :
      EuclideanSpace ℂ (Fin N × Fin N))‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact norm_mulVec_le_matrixVecNorm_mul Q x

open scoped Matrix.Norms.L2Operator in
/-- APSSS Lemma 2.6 in its operator-norm form.  The threshold retains the
source normalization `‖Q‖/(10√N)`; it follows by complementing the
Frobenius-small event at `ε = 1/10`. -/
theorem one_le_two_mul_uniformSphere_large
    {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    1 ≤ 2 * uniformSphere N
      {v |
        ‖Q‖ / (10 * Real.sqrt N) ≤
          ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
            EuclideanSpace ℂ (Fin N))‖} := by
  by_cases hQ : Q = 0
  · subst Q
    simp
  let a : ℝ := ‖Q‖ / (10 * Real.sqrt N)
  let F : ℝ := ‖(WithLp.toLp 2 (Matrix.vec Q) :
    EuclideanSpace ℂ (Fin N × Fin N))‖
  let b : ℝ := (1 / 10 : ℝ) / Real.sqrt N * F
  let bad : Set (EuclideanSpace ℂ (Fin N)) :=
    {v | ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
      EuclideanSpace ℂ (Fin N))‖ < a}
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hop : ‖Q‖ ≤ F := l2OperatorNorm_le_matrixVecNorm Q
  have hab : a ≤ b := by
    dsimp [a, b]
    calc
      ‖Q‖ / (10 * Real.sqrt N) ≤ F / (10 * Real.sqrt N) := by
        gcongr
      _ = (1 / 10 : ℝ) / Real.sqrt N * F := by field_simp
  have hsmall := uniformSphere_mulVec_small_frobenius hN Q hQ
    (ε := (1 / 10 : ℝ)) (by norm_num)
  change uniformSphere N (mulVecNormLeEvent Q b) ≤
    ENNReal.ofReal (5 * (1 / 10 : ℝ)) at hsmall
  have hbadSub : bad ⊆ mulVecNormLeEvent Q b := by
    intro v hv
    exact le_trans hv.le hab
  have hbad : uniformSphere N bad ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      uniformSphere N bad ≤ uniformSphere N (mulVecNormLeEvent Q b) :=
        measure_mono hbadSub
      _ ≤ ENNReal.ofReal (5 * (1 / 10 : ℝ)) := hsmall
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by norm_num
  have hbadMeas : MeasurableSet bad := by
    dsimp [bad, a]
    exact measurableSet_lt (by fun_prop) measurable_const
  have hlarge :
      {v : EuclideanSpace ℂ (Fin N) | a ≤
        ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
          EuclideanSpace ℂ (Fin N))‖} = badᶜ := by
    ext v
    simp [bad]
  have hcompl : uniformSphere N badᶜ = 1 - uniformSphere N bad :=
    prob_compl_eq_one_sub hbadMeas
  have hofhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hhalfEq : ENNReal.ofReal (1 / 2 : ℝ) =
      1 - ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hofhalf, ENNReal.one_sub_inv_two]
  have hhalfLarge : ENNReal.ofReal (1 / 2 : ℝ) ≤ uniformSphere N badᶜ := by
    rw [hcompl, hhalfEq]
    exact tsub_le_tsub_left hbad 1
  change 1 ≤ 2 * uniformSphere N
    {v | a ≤ ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
      EuclideanSpace ℂ (Fin N))‖}
  rw [hlarge]
  calc
    1 = 2 * ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [hofhalf, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ ≤ 2 * uniformSphere N badᶜ := by gcongr

end PSSSNative.BlockBand.PSSS
