module

public import BlockBand.Coarea.Native.BlockBand.Counting.CountLpBounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Exponential count bounds from factorial moments

This file formalizes the binomial (falling-factorial) step of the counting
theorem.  It converts a family of factorial moment estimates into the
Poisson-type exponential-moment bound, keeping the finite spectral dimension
and all constants explicit.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

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
theorem integral_exp_count_le_of_factorialMoments
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

/-- PSSS factorial moments imply the Poisson-type exponential count bound.
This is the exponential count estimate before the specialization to unfolded
windows. -/
theorem psss_countExponential
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b t : ℝ) (hab : a ≤ b) (ht : 0 ≤ t) :
    let q := input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)
    ∫ ω, Real.exp
        (t * (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) ∂M.P ≤
      Real.exp (q * (Real.exp t - 1)) := by
  dsimp only
  let N : M.Ω → ℕ := fun ω =>
    BlockGUE.intervalCount M A₀ (Set.Icc a b) ω
  let D : ℕ := Fintype.card (BlockGUE.Index d)
  let q : ℝ := input.C * (D : ℝ) * (b - a)
  have hq : 0 ≤ q :=
    mul_nonneg (mul_nonneg input.C_nonneg (Nat.cast_nonneg _)) (sub_nonneg.mpr hab)
  apply integral_exp_count_le_of_factorialMoments M.P N D q t
  · intro ω
    calc
      N ω ≤ eigenCount (BlockGUE.deformed M A₀ ω) Set.univ :=
        eigenCount_mono _ (Set.subset_univ _)
      _ = D := by simp [D]
  · exact hq
  · exact ht
  · intro r hr
    exact input.factorialIntegrable hd M A₀ a b r
  · intro r hr
    cases r with
    | zero =>
        simp [N]
    | succ r =>
        simpa [N, q, D] using
          input.factorialCount hd M A₀ a b hab (r + 1)
            (Nat.succ_le_succ (Nat.zero_le r))

end CoareaNative.BlockBand
