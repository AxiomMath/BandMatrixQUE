module
public import Mathlib

/-!
# Exponential moments from factorial moments

The finite falling-factorial expansion of `exp (t N)` converts factorial moment bounds for
a bounded natural-valued count into an exponential-moment bound.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory
open scoped BigOperators
universe u

/-- Finite falling-factorial expansion of `exp (tN)`. -/
theorem exp_natCast_eq_sum_descFactorial (N : ℕ) (t : ℝ) :
    Real.exp (t * N) =
      ∑ r ∈ Finset.range (N + 1),
        (N.descFactorial r : ℝ) / (r.factorial : ℝ) *
          (Real.exp t - 1) ^ r := by
  rw [mul_comm, Real.exp_nat_mul]
  conv_lhs => rw [show Real.exp t = (Real.exp t - 1) + 1 by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro r hr
  rw [one_pow, mul_one]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The same expansion over any ambient range containing the count.  Terms
above `N` vanish because the descending factorial is zero. -/
theorem exp_natCast_eq_sum_descFactorial_range
    (N D : ℕ) (hND : N ≤ D) (t : ℝ) :
    Real.exp (t * N) =
      ∑ r ∈ Finset.range (D + 1),
        (N.descFactorial r : ℝ) / (r.factorial : ℝ) *
          (Real.exp t - 1) ^ r := by
  rw [exp_natCast_eq_sum_descFactorial N t]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ hND)
  · intro r hrD hrN
    have hNr : N < r := by
      exact Nat.lt_of_not_ge (by simpa using hrN)
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hNr]
    simp

/-- Abstract exponential-moment consequence of factorial moment bounds.
The count is deterministically bounded by `D`, as every finite spectral count
is bounded by the matrix dimension. -/
theorem conditional_integral_exp_count_le_of_factorialMoments
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (D : ℕ) (q t : ℝ)
    (hND : ∀ ω, N ω ≤ D) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hint : ∀ r ∈ Finset.range (D + 1),
      Integrable (fun ω => ((N ω).descFactorial r : ℝ)) μ)
    (hfac : ∀ r ∈ Finset.range (D + 1),
      ∫ ω, ((N ω).descFactorial r : ℝ) ∂μ ≤ q ^ r) :
    ∫ ω, Real.exp (t * N ω) ∂μ ≤
      Real.exp (q * (Real.exp t - 1)) := by
  have hpoint (ω : Ω) :
      Real.exp (t * N ω) =
        ∑ r ∈ Finset.range (D + 1),
          ((N ω).descFactorial r : ℝ) / (r.factorial : ℝ) *
            (Real.exp t - 1) ^ r :=
    exp_natCast_eq_sum_descFactorial_range (N ω) D (hND ω) t
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum]
  · calc
      ∑ r ∈ Finset.range (D + 1),
          ∫ ω, ((N ω).descFactorial r : ℝ) / (r.factorial : ℝ) *
            (Real.exp t - 1) ^ r ∂μ =
        ∑ r ∈ Finset.range (D + 1),
          (∫ ω, ((N ω).descFactorial r : ℝ) ∂μ) /
            (r.factorial : ℝ) * (Real.exp t - 1) ^ r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← integral_div, integral_mul_const]
      _ ≤ ∑ r ∈ Finset.range (D + 1),
          q ^ r / (r.factorial : ℝ) * (Real.exp t - 1) ^ r := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hfac r hr) (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)) r)
      _ = ∑ r ∈ Finset.range (D + 1),
          (q * (Real.exp t - 1)) ^ r / (r.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [mul_pow]
          ring
      _ ≤ Real.exp (q * (Real.exp t - 1)) :=
        Real.sum_le_exp_of_nonneg
          (mul_nonneg hq (sub_nonneg.mpr (Real.one_le_exp ht))) (D + 1)
  · intro r hr
    exact ((hint r hr).div_const _).mul_const _

end BlockBand.Counting
