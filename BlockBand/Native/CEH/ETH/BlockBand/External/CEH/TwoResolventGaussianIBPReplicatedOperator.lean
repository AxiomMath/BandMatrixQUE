module
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedCovariance

/-!
# The covariance operator of the replicated GUE coordinates

The covariance operator of the normalized replicated GUE coordinates is the diagonal operator of
the coordinate variances, with operator norm exactly `1/(N d)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open CEHNative.BlockBand
open scoped NNReal RealInnerProductSpace

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

/-- Diagonal vector of exact replicated GUE coordinate variances. -/
def covarianceDiagonal (N d : ℕ) :
    Fin (Fintype.card (HermitianCoordinate (N * d))) → ℝ := fun k =>
  hermitianGUEFinCoordinateVariance (N * d)
    (1 / ((N * d : ℕ) : ℝ)) (by positivity) k

/-- Matrix of the covariance operator in the standard Euclidean basis. -/
theorem covarianceOperator_toMatrix (N d : ℕ) :
    LinearMap.toMatrixOrthonormal
      (EuclideanSpace.basisFun _ ℝ)
      (covarianceOperator (measure N d)).toLinearMap =
      Matrix.diagonal (covarianceDiagonal N d) := by
  have hmem : MemLp (id : CoordinateEuclideanSpace N d →
      CoordinateEuclideanSpace N d) 2 (measure N d) := IsGaussian.memLp_id _ 2 (by simp)
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  change ⟪(EuclideanSpace.basisFun _ ℝ) i,
      (covarianceOperator (measure N d))
        ((EuclideanSpace.basisFun _ ℝ) j)⟫ =
    if i = j then covarianceDiagonal N d i else 0
  rw [real_inner_comm, covarianceOperator_inner hmem]
  simp_rw [EuclideanSpace.basisFun_inner]
  have hmean (k) : (∫ x : CoordinateEuclideanSpace N d, x k ∂measure N d) = 0 := by
    rw [(coordinate_hasLaw N d k).integral_eq]
    exact integral_id_gaussianReal
  have hcov := covariance_eq_sub
    ((coordinate_hasLaw N d j).hasGaussianLaw.memLp_two)
    ((coordinate_hasLaw N d i).hasGaussianLaw.memLp_two)
  rw [hmean j, hmean i, mul_zero, sub_zero] at hcov
  change (∫ z : CoordinateEuclideanSpace N d,
    ((fun x : CoordinateEuclideanSpace N d => x j) *
      (fun x : CoordinateEuclideanSpace N d => x i)) z ∂measure N d) =
      (if i = j then covarianceDiagonal N d i else 0)
  rw [← hcov]
  rw [covariance_coordinate j i]
  unfold covarianceDiagonal
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Ne.symm hji]

/-- The covariance operator itself is the diagonal matrix operator whose
entries are the exact replicated-GUE coordinate variances. -/
theorem covarianceOperator_eq_toEuclideanCLM (N d : ℕ) :
    covarianceOperator (measure N d) =
      (Matrix.toEuclideanCLM (n :=
        Fin (Fintype.card (HermitianCoordinate (N * d)))) (𝕜 := ℝ))
        (Matrix.diagonal (covarianceDiagonal N d)) := by
  have hlin :
      (covarianceOperator (measure N d)).toLinearMap =
        ((Matrix.toEuclideanCLM (n :=
          Fin (Fintype.card (HermitianCoordinate (N * d)))) (𝕜 := ℝ))
          (Matrix.diagonal (covarianceDiagonal N d))).toLinearMap := by
    apply (LinearMap.toMatrixOrthonormal
      (EuclideanSpace.basisFun _ ℝ)).injective
    change LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun _ ℝ)
        (covarianceOperator (measure N d)).toLinearMap =
      LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun _ ℝ)
        (((Matrix.toEuclideanCLM (n :=
          Fin (Fintype.card (HermitianCoordinate (N * d)))) (𝕜 := ℝ))
          (Matrix.diagonal (covarianceDiagonal N d))).toLinearMap)
    rw [covarianceOperator_toMatrix]
    symm
    exact (LinearMap.toMatrixOrthonormal
      (EuclideanSpace.basisFun _ ℝ)).apply_symm_apply _
  ext x i
  exact congrArg (fun y : CoordinateEuclideanSpace N d => y i)
    (LinearMap.congr_fun hlin x)

/-- The finite diagonal covariance vector has supremum norm exactly
`1/(N*d)`: diagonal matrix coordinates attain it, while paired
off-diagonal real/imaginary coordinates have half that variance. -/
theorem norm_covarianceDiagonal {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    ‖covarianceDiagonal N d‖ = 1 / (((N * d : ℕ) : ℝ)) := by
  have hc : 0 ≤ 1 / (((N * d : ℕ) : ℝ)) := by positivity
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg hc]
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact coordinateVariance_le hN hd k
    · exact NNReal.coe_nonneg _
  · obtain ⟨k, hk⟩ := exists_coordinateVariance_eq hN hd
    calc
      1 / (((N * d : ℕ) : ℝ)) = ‖covarianceDiagonal N d k‖ := by
        unfold covarianceDiagonal
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact hk.symm
      _ ≤ ‖covarianceDiagonal N d‖ := norm_le_pi_norm _ _

/-- Exact operator norm of the covariance of normalized replicated GUE
coordinates.  The normalization is `1/(N*d)`, not merely an upper bound. -/
theorem norm_covarianceOperator_measure {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) :
    ‖covarianceOperator (measure N d)‖ =
      1 / (((N * d : ℕ) : ℝ)) := by
  rw [covarianceOperator_eq_toEuclideanCLM]
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  rw [Matrix.l2_opNorm_diagonal]
  exact norm_covarianceDiagonal hN hd

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
