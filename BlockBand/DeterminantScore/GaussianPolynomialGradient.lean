module
public import BlockBand.DeterminantScore.GaussianPolynomialGradient.GaussianGradientAssembly
public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# The Gaussian polynomial gradient lemma

For `2 ≤ p < 3` and a degree bound `k` there is `C > 0` such that, for every finite index type `J`
and every nonzero real polynomial `P` on `J` of total degree at most `k`, under the standard
Gaussian measure on `EuclideanSpace ℝ J`: `P ≠ 0` almost surely, `|∇P|^p |P|^{2-p}` is integrable,
and `E |∇P|^p |P|^{2-p} ≤ C E P²` (`gaussian_polynomial_gradient_manuscript`). The zero set of `P`
is null because it is Lebesgue null and the Gaussian is absolutely continuous.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory ProbabilityTheory WithLp
variable {ι : Type*} [Fintype ι]
/-- The zero set of a nonzero polynomial is null for the product Gaussian (it is Lebesgue null). -/
theorem standardGaussianCoordinates_polynomial_zero_null
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    standardGaussianCoordinates {x : ι → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  have hac : standardGaussianCoordinates (ι := ι) ≪ (volume : Measure (ι → ℝ)) :=
    BlockBand.Parameters.pi_absolutelyContinuous_volume _
      (fun _ => gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0))
  exact hac (BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype P hP)
/-- The zero set of a nonzero polynomial is null for `stdGaussian` in every finite dimension. -/
theorem standardGaussian_polynomialValue_zero_null
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    stdGaussian (EuclideanSpace ℝ ι) {x | polynomialValue P x = 0} = 0 := by
  rw [← standardGaussianCoordinates_toLp]
  rw [Measure.map_apply (by fun_prop)
    (isClosed_eq (continuous_polynomialValue P) continuous_const).measurableSet]
  change standardGaussianCoordinates {x : ι → ℝ | MvPolynomial.eval x P = 0} = 0
  exact standardGaussianCoordinates_polynomial_zero_null P hP
/-- A nonzero polynomial is almost surely nonzero under `stdGaussian`. -/
theorem ae_standardGaussian_polynomialValue_ne_zero
    (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ ι), polynomialValue P x ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using standardGaussian_polynomialValue_zero_null P hP
universe u
omit [Fintype ι] in
/-- **The Gaussian polynomial gradient lemma.** The positive constant is chosen before the
dimension and the polynomial. -/
theorem gaussian_polynomial_gradient_manuscript (k : ℕ) (p : ℝ)
    (hp2 : 2 ≤ p) (hp3 : p < 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type u) [Fintype J] (P : MvPolynomial J ℝ),
      P ≠ 0 → P.totalDegree ≤ k →
        (∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ J), polynomialValue P x ≠ 0) ∧
        Integrable (gradientWeighted P p) (stdGaussian (EuclideanSpace ℝ J)) ∧
          (∫ x : EuclideanSpace ℝ J, gradientWeighted P p x ∂stdGaussian (EuclideanSpace ℝ J)) ≤
            C * (∫ x : EuclideanSpace ℝ J, polynomialValue P x ^ 2 ∂stdGaussian (EuclideanSpace ℝ J)) := by
  obtain ⟨C, hC, hall⟩ := exists_gaussian_polynomial_gradient_constant.{u} k p hp2 hp3
  refine ⟨C, hC, ?_⟩
  intro J _ P hP0 hP
  exact ⟨ae_standardGaussian_polynomialValue_ne_zero P hP0, hall J P hP0 hP⟩
end BlockBand.DeterminantScore.GaussianGradient
