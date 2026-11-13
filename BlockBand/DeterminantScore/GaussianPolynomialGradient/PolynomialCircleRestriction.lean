module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

/-!
# Restriction of a real polynomial to a rotation circle

For vectors `X, Y` and `z = e^{iθ}`, the rotated coordinate `X_i cos θ + Y_i sin θ` is `z⁻¹` times
the quadratic polynomial `coordinateNumerator X Y i` evaluated at `z`; hence for a real polynomial
`P` of total degree at most `k`, `z^k P(X cos θ + Y sin θ)` is the value at `z` of the complex
polynomial `circleRestriction P k X Y`, of degree at most `2k`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic numerator of the coordinate `X_i cos θ + Y_i sin θ` in `z = e^{iθ}`. -/
def coordinateNumerator (X Y : ι → ℝ) (i : ι) : Polynomial ℂ :=
  Polynomial.C (((X i : ℂ) - Complex.I * (Y i : ℂ)) / 2) * Polynomial.X ^ 2 +
    Polynomial.C (((X i : ℂ) + Complex.I * (Y i : ℂ)) / 2)

/-- The polynomial `Q` with `Q(e^{iθ}) = e^{ikθ} P(X cos θ + Y sin θ)`. -/
def circleRestriction (P : MvPolynomial ι ℝ) (k : ℕ) (X Y : ι → ℝ) : Polynomial ℂ :=
  ∑ s ∈ P.support, Polynomial.C (P.coeff s : ℂ) *
    (Polynomial.X ^ (k - ∑ i, s i) * ∏ i, coordinateNumerator X Y i ^ s i)

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate numerator has degree at most two. -/
theorem coordinateNumerator_natDegree_le (X Y : ι → ℝ) (i : ι) :
    (coordinateNumerator X Y i).natDegree ≤ 2 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  simp only [max_le_iff]
  constructor
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · simp

omit [DecidableEq ι] in
/-- Every monomial in the support of `P` has total degree at most `k`. -/
theorem support_degree_le (P : MvPolynomial ι ℝ) (k : ℕ)
    (hP : P.totalDegree ≤ k) (s : ι →₀ ℕ) (hs : s ∈ P.support) :
    (∑ i, s i) ≤ k := by
  have hd := (MvPolynomial.le_totalDegree hs).trans hP
  simpa [Finsupp.sum_fintype] using hd

omit [DecidableEq ι] in
/-- The circle restriction has degree at most `2k`, in every finite dimension, when
`P.totalDegree ≤ k`. -/
theorem circleRestriction_natDegree_le (P : MvPolynomial ι ℝ) (k : ℕ)
    (X Y : ι → ℝ) (hP : P.totalDegree ≤ k) :
    (circleRestriction P k X Y).natDegree ≤ 2 * k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have hd := support_degree_le P k hP s hs
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have hp : (∏ i, coordinateNumerator X Y i ^ s i).natDegree ≤ 2 * ∑ i, s i := by
    refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
    calc
      ∑ i, (coordinateNumerator X Y i ^ s i).natDegree ≤ ∑ i, s i * 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_pow_le_of_le (s i) (coordinateNumerator_natDegree_le X Y i)
      _ = 2 * ∑ i, s i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; omega
  have hx : (Polynomial.X ^ (k - ∑ i, s i) : Polynomial ℂ).natDegree = k - ∑ i, s i := by simp
  rw [hx]
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- On the unit circle, the coordinate numerator equals `z` times the rotated real coordinate. -/
theorem coordinateNumerator_eval_circle (X Y : ι → ℝ) (i : ι) (θ : ℝ) :
    (coordinateNumerator X Y i).eval (Complex.exp (θ * Complex.I)) =
      Complex.exp (θ * Complex.I) *
        ((Real.cos θ * X i + Real.sin θ * Y i : ℝ) : ℂ) := by
  simp only [coordinateNumerator, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Complex.exp_mul_I]
  push_cast
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have htrig := Real.sin_sq_add_cos_sq θ
  have htrigC : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast htrig
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  linear_combination -((X i : ℂ) + Complex.I * (Y i : ℂ)) / 2 * htrigC

omit [DecidableEq ι] in
/-- On the unit circle, the circle restriction equals `z^k P(X cos θ + Y sin θ)`. -/
theorem circleRestriction_eval_circle (P : MvPolynomial ι ℝ) (k : ℕ)
    (X Y : ι → ℝ) (hP : P.totalDegree ≤ k) (θ : ℝ) :
    (circleRestriction P k X Y).eval (Complex.exp (θ * Complex.I)) =
      Complex.exp (θ * Complex.I) ^ k *
        ((MvPolynomial.eval (fun i => Real.cos θ * X i + Real.sin θ * Y i) P : ℝ) : ℂ) := by
  rw [MvPolynomial.eval_eq']
  simp only [circleRestriction, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_prod,
    coordinateNumerator_eval_circle]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hd := support_degree_le P k hP s hs
  have he : k - (∑ i, s i) + (∑ i, s i) = k := Nat.sub_add_cancel hd
  have hpowers : Complex.exp (θ * Complex.I) ^ (k - ∑ i, s i) *
      Complex.exp (θ * Complex.I) ^ (∑ i, s i) = Complex.exp (θ * Complex.I) ^ k := by
    rw [← pow_add, he]
  rw [← mul_assoc (Complex.exp (θ * Complex.I) ^ (k - ∑ i, s i))
    (Complex.exp (θ * Complex.I) ^ (∑ i, s i)), hpowers]
  ring

end BlockBand.DeterminantScore.GaussianGradient
