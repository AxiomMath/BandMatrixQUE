module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# Real polynomials under the standard Gaussian coordinate measure

`standardGaussianCoordinates` is the product of independent standard real Gaussians. Polynomials
and their squares are integrable; the chain rule along a curve and the derivative of a polynomial
along the rotation `X cos θ + Y sin θ` are expressed through the directional derivative
`polynomialDirectional`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of independent standard real Gaussians on `ι → ℝ`. -/
def standardGaussianCoordinates : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

/-- Every integer moment of the standard real Gaussian is integrable. -/
theorem integrable_gaussian_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have hn := (memLp_id_gaussianReal' (μ := 0) (v := 1) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  refine hn.mono' (by fun_prop) ?_
  filter_upwards with x
  simp only [norm_pow, id_eq]
  exact le_rfl

omit [DecidableEq ι] in
/-- Every polynomial is integrable under the Gaussian coordinate measure (from the monomial
moments). -/
theorem integrable_polynomial_standardGaussian (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P) standardGaussianCoordinates := by
  have heq : (fun x : ι → ℝ => MvPolynomial.eval x P) =
      fun x => ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i := by
    funext x
    exact MvPolynomial.eval_eq' x P
  rw [heq]
  apply integrable_finsetSum P.support
  intro d hd
  exact (Integrable.fintype_prod (fun i : ι => integrable_gaussian_pow (d i))).const_mul (P.coeff d)

omit [DecidableEq ι] in
/-- The square of a polynomial is integrable under the Gaussian coordinate measure. -/
theorem integrable_polynomial_sq_standardGaussian (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P ^ 2) standardGaussianCoordinates := by
  convert integrable_polynomial_standardGaussian (P ^ 2) using 1
  funext x
  exact ((MvPolynomial.eval x).map_pow P 2).symm

/-- The directional derivative `Σ_i ∂_i P(x) v_i`. -/
def polynomialDirectional (P : MvPolynomial ι ℝ) (x v : ι → ℝ) : ℝ :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) * v i

/-- The chain rule for a polynomial along a differentiable curve, from the coordinate derivatives. -/
theorem hasDerivAt_polynomial_curve (P : MvPolynomial ι ℝ) (x : ι → ℝ → ℝ)
    (v : ι → ℝ) (θ : ℝ) (hx : ∀ i, HasDerivAt (x i) (v i) θ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun i => x i t) P)
      (polynomialDirectional P (fun i => x i θ) v) θ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simpa [polynomialDirectional] using hasDerivAt_const θ a
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    · funext t
      exact (MvPolynomial.eval (fun i => x i t)).map_add P Q
    · simp [polynomialDirectional, map_add, Finset.sum_add_distrib, add_mul]
  | mul_X P j hP =>
    have h := hP.mul (hx j)
    convert h using 1
    · funext t
      simp
    · simp [polynomialDirectional, MvPolynomial.pderiv_X, Pi.single_apply,
        map_add, map_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
      simp [apply_ite]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The rotated point `X cos θ + Y sin θ`. -/
def rotatedCoordinates (X Y : ι → ℝ) (θ : ℝ) : ι → ℝ :=
  fun i => Real.cos θ * X i + Real.sin θ * Y i

/-- The rotated velocity `-X sin θ + Y cos θ`. -/
def rotatedVelocity (X Y : ι → ℝ) (θ : ℝ) : ι → ℝ :=
  fun i => -Real.sin θ * X i + Real.cos θ * Y i

omit [Fintype ι] [DecidableEq ι] in
/-- The derivative of a rotated coordinate. -/
theorem hasDerivAt_rotated_coordinate (X Y : ι → ℝ) (θ : ℝ) (i : ι) :
    HasDerivAt (fun t : ℝ => rotatedCoordinates X Y t i) (rotatedVelocity X Y θ i) θ := by
  exact ((Real.hasDerivAt_cos θ).mul_const (X i)).add
    ((Real.hasDerivAt_sin θ).mul_const (Y i))

/-- The derivative of a polynomial along the rotation is the directional derivative in the
rotated velocity. -/
theorem hasDerivAt_polynomial_rotation (P : MvPolynomial ι ℝ) (X Y : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (rotatedCoordinates X Y t) P)
      (polynomialDirectional P (rotatedCoordinates X Y θ) (rotatedVelocity X Y θ)) θ :=
  hasDerivAt_polynomial_curve P (fun i t => rotatedCoordinates X Y t i)
    (rotatedVelocity X Y θ) θ (hasDerivAt_rotated_coordinate X Y θ)

end BlockBand.DeterminantScore.GaussianGradient
