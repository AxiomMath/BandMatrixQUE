module

public import BlockBand.Prelude

/-!
# Pointwise determinant-square Jacobi identities

Exact pointwise identities along real affine lines `A + tH` of finite complex square matrices,
used for the determinant score and the sector integration by parts: Jacobi's formula, the
derivative of `Complex.normSq (det (A + tH))`, and the vanishing of that derivative on the
determinant hypersurface. No measure is involved. The logarithmic identity requires
invertibility; the zero-determinant cancellation does not.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore

open Matrix Polynomial
open scoped Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant polynomial of the affine matrix line `A + t Q`.

This is the exact algebraic precursor of the determinant derivative in the
passive-log argument. -/
noncomputable def detLinePoly [CommRing R] (A Q : Matrix ι ι R) : R[X] :=
  (A.map (C : R →+* R[X]) + (X : R[X]) • Q.map (C : R →+* R[X])).det

/-- An invertible affine matrix line factors through its base point.

This is the matrix factorization underlying Jacobi's formula. -/
theorem map_add_X_smul_eq_mul [CommRing R] (A Q : Matrix ι ι R)
    (hA : IsUnit A.det) :
    A.map (C : R →+* R[X]) + (X : R[X]) • Q.map (C : R →+* R[X]) =
      A.map (C : R →+* R[X]) * (1 + (X : R[X]) • (A⁻¹ * Q).map (C : R →+* R[X])) := by
  rw [Matrix.mul_add, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_smul]
  congr 1
  rw [← Matrix.map_mul, ← Matrix.mul_assoc, A.mul_nonsing_inv hA, Matrix.one_mul]

/-- Formal-polynomial Jacobi identity at an invertible base matrix:

`d/dt det(A + tQ)|_{t=0} = det(A) * tr(A⁻¹ Q)`.

The source normalization is the affine line `A + tQ`; the derivative
is the formal polynomial derivative and is evaluated at zero. -/
theorem eval_derivative_detLinePoly [CommRing R] (A Q : Matrix ι ι R)
    (hA : IsUnit A.det) :
    (derivative (detLinePoly A Q)).eval 0 = A.det * (A⁻¹ * Q).trace := by
  rw [detLinePoly, map_add_X_smul_eq_mul A Q hA, Matrix.det_mul]
  have hdet : (A.map (C : R →+* R[X])).det = C A.det :=
    (RingHom.map_det (C : R →+* R[X]) A).symm
  rw [derivative_mul, eval_add, eval_mul, eval_mul, hdet]
  rw [derivative_C, eval_zero, zero_mul, zero_add, eval_C]
  rw [Matrix.derivative_det_one_add_X_smul]

/-- Evaluating the formal affine determinant polynomial gives the affine determinant. -/
theorem eval_detLinePoly_complex (A H : Matrix ι ι ℂ) (z : ℂ) :
    (detLinePoly A H).eval z = (A + z • H).det := by
  unfold detLinePoly
  change (Polynomial.evalRingHom z)
      (A.map (Polynomial.C : ℂ →+* Polynomial ℂ) +
        (Polynomial.X : Polynomial ℂ) •
          H.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det =
    (A + z • H).det
  rw [(Polynomial.evalRingHom z).map_det]
  congr 1
  ext i j
  simp
  ring

/-- The determinant on a real affine matrix line is differentiable even at a singular
base.  Its derivative is recorded by the formal derivative of `detLinePoly`; the
invertible specialization below identifies it with the Jacobi trace. -/
theorem hasDerivAt_det_realAffineLine_general (A H : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℝ => (A + (t : ℂ) • H).det)
      ((Polynomial.derivative (detLinePoly A H)).eval 0) 0 := by
  have hp := (detLinePoly A H).hasDerivAt (0 : ℂ)
  have hr := hp.comp_ofReal
  simpa only [eval_detLinePoly_complex, Complex.ofReal_zero] using hr

/-- Real differentiation of the complex determinant along `A + t H` at an invertible base
(Jacobi's formula). -/
theorem hasDerivAt_det_realAffineLine (A H : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    HasDerivAt (fun t : ℝ => (A + (t : ℂ) • H).det)
      (A.det * (A⁻¹ * H).trace) 0 := by
  have hp := (detLinePoly A H).hasDerivAt (0 : ℂ)
  rw [eval_derivative_detLinePoly A H hA] at hp
  have hr := hp.comp_ofReal
  simpa only [eval_detLinePoly_complex, Complex.ofReal_zero] using hr

/-- Pointwise derivative of the determinant-square density.

For the weight `det(M)^2` on Hermitian matrices this is its phase-free complex form
`Complex.normSq (det M)`. The factor `2` is the normalization used before Gaussian integration by
parts in the sector integration-by-parts lemma. -/
theorem hasDerivAt_normSq_det_realAffineLine (A H : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    HasDerivAt (fun t : ℝ => Complex.normSq ((A + (t : ℂ) • H).det))
      (2 * Complex.normSq A.det * ((A⁻¹ * H).trace).re) 0 := by
  have hdet := hasDerivAt_det_realAffineLine A H hA
  have hsq := hdet.norm_sq
  have hinner :
      inner ℝ A.det (A.det * (A⁻¹ * H).trace) =
        Complex.normSq A.det * ((A⁻¹ * H).trace).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply', ← mul_assoc,
      ← Complex.normSq_eq_conj_mul_self]
    simp
  convert hsq using 1
  · simp only [Complex.sq_norm]
  · simp only [Complex.ofReal_zero, zero_smul, add_zero, hinner]
    ring

/-- The determinant-square derivative factors as the determinant-square weight times the
real Jacobi score. -/
theorem hasDerivAt_normSq_det_realAffineLine_score (A H : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    HasDerivAt (fun t : ℝ => Complex.normSq ((A + (t : ℂ) • H).det))
      (Complex.normSq A.det * (2 * ((A⁻¹ * H).trace).re)) 0 := by
  convert hasDerivAt_normSq_det_realAffineLine A H hA using 1
  ring

/-- On the determinant hypersurface the determinant-square weight has zero first derivative in
every affine direction.

This is the local algebraic cancellation behind the absence of a first-order boundary term in the
sector integration by parts. It does not by itself justify weak differentiation of the
discontinuous inertia-sector indicator. -/
theorem hasDerivAt_normSq_det_realAffineLine_of_det_eq_zero
    (A H : Matrix ι ι ℂ) (hA : A.det = 0) :
    HasDerivAt (fun t : ℝ => Complex.normSq ((A + (t : ℂ) • H).det)) 0 0 := by
  have hdet := hasDerivAt_det_realAffineLine_general A H
  have hsq := hdet.norm_sq
  simpa only [Complex.sq_norm, Complex.ofReal_zero, zero_smul, add_zero, hA,
    inner_zero_left, mul_zero] using hsq

/-- Logarithmic determinant-square score along a real affine matrix line.

At a nonsingular base matrix the derivative of `log ‖det(A+tH)‖²` is exactly
`2 Re tr(A⁻¹H)`.  No sector indicator or expectation is present in this statement. -/
theorem hasDerivAt_log_normSq_det_realAffineLine (A H : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    HasDerivAt
      (fun t : ℝ => Real.log (Complex.normSq ((A + (t : ℂ) • H).det)))
      (2 * ((A⁻¹ * H).trace).re) 0 := by
  have hn : Complex.normSq A.det ≠ 0 := by
    exact (Complex.normSq_eq_zero.not.mpr hA.ne_zero)
  have hsq := hasDerivAt_normSq_det_realAffineLine A H hA
  have hbase :
      Complex.normSq ((A + ((0 : ℝ) : ℂ) • H).det) ≠ 0 := by
    simpa using hn
  have hlog := hsq.log hbase
  have hscore :
      2 * Complex.normSq A.det * ((A⁻¹ * H).trace).re /
          Complex.normSq A.det =
        2 * ((A⁻¹ * H).trace).re := by
    field_simp
  convert hlog using 1
  · simpa only [Complex.ofReal_zero, zero_smul, add_zero] using hscore.symm

end BlockBand.DeterminantScore
