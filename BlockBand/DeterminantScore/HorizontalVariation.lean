module

public import BlockBand.DeterminantScore.PointwiseJacobi

/-!
# Hermitian rank-two horizontal score algebra

The trace algebra of the determinant score. The domain is finite complex matrices and vectors; the
real pairing is `Re(Σ_i conj(h_i) z_i)`. For a Hermitian conditional inverse `R` and `k = Q K₀ v`,
the parallel-frame variation is `-(h k* + k h*)` and its real Jacobi score is `-4 Re(h* R k)`.
No probability law is involved.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex outer product with conjugation on the second vector. -/
def rankOne (u v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => u i * star (v j)

omit [DecidableEq ι] in
/-- The trace of a matrix times a rank-one outer product is its vector pairing. -/
theorem trace_mul_rankOne (R : Matrix ι ι ℂ) (u v : ι → ℂ) :
    (R * rankOne u v).trace = dotProduct (star v) (R *ᵥ u) := by
  change (∑ i, ∑ j, R i j * (u j * star (v i))) =
    ∑ i, star (v i) * (∑ j, R i j * u j)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq ι] in
/-- Hermitian pairings have equal real parts under exchange of the two vectors. -/
theorem re_pairing_exchange (R : Matrix ι ι ℂ) (hR : R.IsHermitian)
    (h k : ι → ℂ) :
    (dotProduct (star k) (R *ᵥ h)).re =
      (dotProduct (star h) (R *ᵥ k)).re := by
  have hentry (i j : ι) : star (R j i) = R i j :=
    congrFun (congrFun hR i) j
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have heq : star (star (h i) * (R i j * k j)) =
      star (k j) * (R j i * h i) := by
    simp only [star_mul, star_star, ← hentry j i]
    ring
  rw [← heq]
  exact Complex.conj_re _

omit [DecidableEq ι] in
/-- Exact `-4` real trace factor for the horizontal rank-two variation. -/
theorem realJacobi_horizontal_rankTwo (R : Matrix ι ι ℂ)
    (hR : R.IsHermitian) (h k : ι → ℂ) :
    2 * ((R * (-(rankOne h k + rankOne k h))).trace).re =
      -4 * (dotProduct (star h) (R *ᵥ k)).re := by
  rw [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add, Matrix.trace_add,
    trace_mul_rankOne, trace_mul_rankOne]
  simp only [Complex.neg_re, Complex.add_re]
  rw [re_pairing_exchange R hR h k]
  ring

/-- Pointwise logarithmic determinant-square derivative in a horizontal rank-two
matrix direction. This proves the `-4` normalization before any sector
indicator, moving-frame expectation, or normalization is introduced. -/
theorem hasDerivAt_log_normSq_det_horizontal_rankTwo
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hunit : IsUnit A.det)
    (h k : ι → ℂ) :
    HasDerivAt
      (fun t : ℝ => Real.log (Complex.normSq
        ((A + (t : ℂ) • (-(rankOne h k + rankOne k h))).det)))
      (-4 * (dotProduct (star h) (A⁻¹ *ᵥ k)).re) 0 := by
  have hs := hasDerivAt_log_normSq_det_realAffineLine A
    (-(rankOne h k + rankOne k h)) hunit
  rw [realJacobi_horizontal_rankTwo A⁻¹ hA.inv h k] at hs
  exact hs

end BlockBand.DeterminantScore
