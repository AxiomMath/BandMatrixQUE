module

public import BlockBand.Native.CEH.ETH.BlockBand.External.PSSS.Interface
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Ordinary count moments from factorial moments

This is the combinatorial step used both by the counting theorem and by the singular-log
argument: ordinary powers are expanded into falling factorials with Stirling numbers, without any
random-matrix assumption.  The theorem works for an arbitrary natural-valued count on an
arbitrary measure space; PSSS enters only when its hypotheses are used to
supply `hfac`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped BigOperators

universe u

/-- An `r`th ordinary moment is the Stirling-weighted sum of the falling
factorial moments, with inequalities propagated coefficientwise. -/
theorem ordinaryMoment_le_of_factorialMoments
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (r : ℕ) (q : ℝ)
    (hint : ∀ j ∈ Finset.range (r + 1),
      Integrable (fun ω => ((N ω).descFactorial j : ℝ)) μ)
    (hfac : ∀ j ∈ Finset.range (r + 1),
      ∫ ω, ((N ω).descFactorial j : ℝ) ∂μ ≤ q ^ j) :
    ∫ ω, (N ω : ℝ) ^ r ∂μ ≤
      ∑ j ∈ Finset.range (r + 1), (r.stirlingSecond j : ℝ) * q ^ j := by
  have hpoint (ω : Ω) :
      (N ω : ℝ) ^ r =
        ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) * ((N ω).descFactorial j : ℝ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (N ω) r
  calc
    ∫ ω, (N ω : ℝ) ^ r ∂μ =
        ∫ ω, ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) * ((N ω).descFactorial j : ℝ) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) *
            ∫ ω, ((N ω).descFactorial j : ℝ) ∂μ := by
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro j hj
            rw [integral_const_mul]
          · intro j hj
            exact (hint j hj).const_mul _
    _ ≤ ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) * q ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hfac j hj) (by positivity)

/-- Ordinary moments from factorial moments: if `E[(N)_j] ≤ q^j` for `j ≤ r` (descending
factorials, integrable), then `E[N^r] ≤ Σ_{j ≤ r} S(r, j) q^j` with Stirling numbers of the second
kind. This is the form used for dyadic shell counts. -/
theorem countMoment_stirlingBound
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (r : ℕ) (q : ℝ)
    (hint : ∀ j ∈ Finset.range (r + 1),
      Integrable (fun ω => ((N ω).descFactorial j : ℝ)) μ)
    (hfac : ∀ j ∈ Finset.range (r + 1),
      ∫ ω, ((N ω).descFactorial j : ℝ) ∂μ ≤ q ^ j) :
    ∫ ω, (N ω : ℝ) ^ r ∂μ ≤
      ∑ j ∈ Finset.range (r + 1), (r.stirlingSecond j : ℝ) * q ^ j :=
  ordinaryMoment_le_of_factorialMoments μ N r q hint hfac

/-- For a scale `0 ≤ v ≤ 1`, the Stirling moment polynomial is linear in
`v` up to its value at unit scale.  This is the small-interval estimate in
the singular-log shell argument. -/
theorem stirlingMomentPolynomial_small
    (r : ℕ) (hr : 1 ≤ r) {C v : ℝ}
    (hC : 0 ≤ C) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (C * v) ^ j ≤
      v * ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * C ^ j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simp [Nat.stirlingSecond_succ_zero]
  · calc
      (r.stirlingSecond j : ℝ) * (C * v) ^ j =
          ((r.stirlingSecond j : ℝ) * C ^ j) * v ^ j := by
            rw [mul_pow]
            ring
      _ ≤ ((r.stirlingSecond j : ℝ) * C ^ j) * v := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_of_le_one hv hv1 hj0
            · positivity
      _ = v * ((r.stirlingSecond j : ℝ) * C ^ j) := by ring

end CEHNative.BlockBand
