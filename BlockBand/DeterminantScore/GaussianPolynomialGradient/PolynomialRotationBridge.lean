module

public import BlockBand.DeterminantScore.GaussianPolynomialGradient.PolynomialGaussianBasics
public import BlockBand.DeterminantScore.GaussianPolynomialGradient.PolynomialCircleRestriction
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The derivative of the circle restriction

The finite-coordinate Gaussian measure maps to `stdGaussian` on Euclidean space; the directional
derivative is the inner product with the Euclidean gradient; and the angular derivative of the
circle restriction `circleRestriction P k X Y` on the unit circle is expressed through the
directional derivative of `P` along the rotation (`circleRestriction_derivative_bridge`,
`circleRestriction_angular_norm`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The finite-coordinate Gaussian maps to `stdGaussian` on `EuclideanSpace ℝ ι`. -/
theorem standardGaussianCoordinates_toLp :
    (standardGaussianCoordinates (ι := ι)).map (toLp 2) =
      stdGaussian (EuclideanSpace ℝ ι) :=
  map_pi_eq_stdGaussian

/-- The Euclidean gradient vector of a real polynomial. -/
def polynomialGradient (P : MvPolynomial ι ℝ) (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => MvPolynomial.eval x (MvPolynomial.pderiv i P))

omit [DecidableEq ι] in
/-- The directional derivative is the inner product with the Euclidean gradient. -/
theorem polynomialDirectional_eq_inner (P : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    polynomialDirectional P x v = ⟪polynomialGradient P x, toLp 2 v⟫_ℝ := by
  simp [polynomialDirectional, polynomialGradient, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- The derivative of `θ ↦ e^{iθ}`. -/
theorem hasDerivAt_circleExp (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp
  simpa using h

/-- The derivative identity of the circle restriction, with the angular derivative expressed
through the partial derivatives of `P`. -/
theorem circleRestriction_derivative_bridge (P : MvPolynomial ι ℝ) (k : ℕ)
    (X Y : ι → ℝ) (hP : P.totalDegree ≤ k) (θ : ℝ) :
    (circleRestriction P k X Y).derivative.eval (Complex.exp (θ * Complex.I)) *
        (Complex.exp (θ * Complex.I) * Complex.I) =
      (k : ℂ) * Complex.exp (θ * Complex.I) ^ (k - 1) *
          (Complex.exp (θ * Complex.I) * Complex.I) *
          (MvPolynomial.eval (rotatedCoordinates X Y θ) P : ℂ) +
        Complex.exp (θ * Complex.I) ^ k *
          (polynomialDirectional P (rotatedCoordinates X Y θ)
            (rotatedVelocity X Y θ) : ℂ) := by
  have he := hasDerivAt_circleExp θ
  have hleft := ((circleRestriction P k X Y).hasDerivAt _).scomp θ he
  have hright := (he.pow k).mul (hasDerivAt_polynomial_rotation P X Y θ).ofReal_comp
  have hf : (fun t : ℝ => (circleRestriction P k X Y).eval (Complex.exp (t * Complex.I))) =
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) ^ k *
        (MvPolynomial.eval (rotatedCoordinates X Y t) P : ℂ)) := by
    funext t
    exact circleRestriction_eval_circle P k X Y hP t
  simp only [Function.comp_def] at hleft
  rw [hf] at hleft
  simpa only [Function.comp_def, smul_eq_mul, Pi.pow_apply, mul_comm] using hleft.unique hright

/-- The norm of the angular numerator is the absolute value of the real directional derivative,
including degree `k = 0`. -/
theorem circleRestriction_angular_norm (P : MvPolynomial ι ℝ) (k : ℕ)
    (X Y : ι → ℝ) (hP : P.totalDegree ≤ k) (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) * (circleRestriction P k X Y).derivative.eval
        (Complex.exp (θ * Complex.I)) - (k : ℂ) *
          (circleRestriction P k X Y).eval (Complex.exp (θ * Complex.I))‖ =
      ‖polynomialDirectional P (rotatedCoordinates X Y θ) (rotatedVelocity X Y θ)‖ := by
  let z : ℂ := Complex.exp (θ * Complex.I)
  have hv := circleRestriction_eval_circle P k X Y hP θ
  have hd := circleRestriction_derivative_bridge P k X Y hP θ
  have hk : (k : ℂ) * z ^ (k - 1) * z = (k : ℂ) * z ^ k := by
    cases k with
    | zero => simp
    | succ k => simp [pow_succ, mul_assoc]
  have he : (z * (circleRestriction P k X Y).derivative.eval z - (k : ℂ) *
      (circleRestriction P k X Y).eval z) * Complex.I = z ^ k *
        (polynomialDirectional P (rotatedCoordinates X Y θ) (rotatedVelocity X Y θ) : ℂ) := by
    rw [hv]
    change (z * (circleRestriction P k X Y).derivative.eval z - (k : ℂ) *
      (z ^ k * (MvPolynomial.eval (rotatedCoordinates X Y θ) P : ℂ))) * Complex.I = _
    have hd' : (circleRestriction P k X Y).derivative.eval z * (z * Complex.I) =
      ((k : ℂ) * z ^ (k - 1) * z) * Complex.I *
          (MvPolynomial.eval (rotatedCoordinates X Y θ) P : ℂ) +
        z ^ k * (polynomialDirectional P (rotatedCoordinates X Y θ) (rotatedVelocity X Y θ) : ℂ) := by
      convert hd using 1
      dsimp [z]
      ring
    rw [hk] at hd'
    linear_combination hd'
  have hz : ‖z‖ = 1 := by dsimp [z]; simp
  have hn := congrArg norm he
  simpa only [norm_mul, Complex.norm_I, norm_pow, hz, one_pow, mul_one, one_mul,
    Complex.norm_real, Real.norm_eq_abs] using hn

end BlockBand.DeterminantScore.GaussianGradient
