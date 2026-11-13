module

public import BlockBand.Coarea.Native.BlockBand.Coarea.GaussianDensityFactor
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairJacobianLocal

/-!
# Algebraic Gaussian factors in eigenpair coarea coordinates

The factors behind the Gaussian regression step of the coarea theorem, combined.  For fixed
exterior compression data, this simultaneously performs the Gaussian regression split, the
consecutive GUE-normalizer cancellation, the normalized projective-chart integration, and
the replacement of the local real Jacobian by the squared Hermitian gap
determinant.

No change-of-variables or global eigenpair coarea theorem is assumed here.  The
equalities are pointwise in the selected energy and all exterior data.  The
matrix size and positive variance are fixed; there are no limit or uniformity
quantifiers.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The complete Gaussian-factor identity after the normalized projective mass
has been evaluated as `π^(d-1)/(d-1)!`.

Here `f` is the selected scalar compression, `q` is the perpendicular exterior
column, and `Fv` is the exterior compression to the orthogonal complement.
The complementary eigenpair block `B` is Hermitian, so its real local Jacobian
is exactly `det(E I - B)^2`. -/
theorem eigenpairGaussianCoareaConstantFactors
    {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    (E f : ℝ) (q : Fin (d - 1) → ℂ)
    (B Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (hB : B.IsHermitian) :
    (((Real.pi ^ (d - 1) / (d - 1).factorial) *
          (gueNormalizer (d - 1) t / gueNormalizer d t)) *
        eigenpairLocalRealJacobianDensity E B) *
      Real.exp
        (-hilbertSchmidtNormSq
          (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B -
            Matrix.fromBlocks ((f : ℂ) • (1 : Matrix Unit Unit ℂ))
              (eigenpairTangentColumn q)ᴴ (eigenpairTangentColumn q) Fv) /
          (2 * t)) =
    (coareaGaussianDensityConstant d t *
        (eigenpairGapMatrix E B).det.re ^ 2) *
      (canonicalGaussianRegressionFactor E f t q *
        Real.exp (-hilbertSchmidtNormSq (B - Fv) / (2 * t))) := by
  rw [projectiveJacobian_mul_gueNormalizerRatio hd ht]
  rw [eigenpairLocalRealJacobianDensity_eq_detGap_sq E hB]
  rw [canonicalGaussianExponentialFactorization E f q B Fv ht]

/-- The algebraic and measure normalization behind the Gaussian regression step.  In
positive projective dimension, the affine density integrates to
the normalized Haar mass, the normalizer ratio becomes `c_{d,t}`, the Gaussian
exponent regresses into selected and complementary factors, and the Jacobian is
the squared gap determinant.

The statement contains no assertion that these coordinates globally change variables on the
Hermitian matrix space. -/
theorem eigenpairGaussianCoareaFactors
    {d : ℕ} (hd : 1 < d) {t : ℝ} (ht : 0 < t)
    (E f : ℝ) (q : Fin (d - 1) → ℂ)
    (B Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (hB : B.IsHermitian) :
    ((((∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
            ((1 + ‖z‖ ^ 2)⁻¹) ^ d) *
          (gueNormalizer (d - 1) t / gueNormalizer d t)) *
        eigenpairLocalRealJacobianDensity E B) *
      Real.exp
        (-hilbertSchmidtNormSq
          (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B -
            Matrix.fromBlocks ((f : ℂ) • (1 : Matrix Unit Unit ℂ))
              (eigenpairTangentColumn q)ᴴ (eigenpairTangentColumn q) Fv) /
          (2 * t))) =
    (coareaGaussianDensityConstant d t *
        (eigenpairGapMatrix E B).det.re ^ 2) *
      (canonicalGaussianRegressionFactor E f t q *
        Real.exp (-hilbertSchmidtNormSq (B - Fv) / (2 * t))) := by
  rw [projectiveChartIntegral_mul_gueNormalizerRatio hd ht]
  rw [eigenpairLocalRealJacobianDensity_eq_detGap_sq E hB]
  rw [canonicalGaussianExponentialFactorization E f q B Fv ht]

end CoareaNative.BlockBand
