module

public import Mathlib

/-!
# Factorial moments to ordinary moments of a count

* `pow_le_descFactorial` — for all `n r : ℕ`, `n^r ≤ 2^r (n)_r + (2r)^r`.
* `count_eLpNorm_le_of_factorial` — if `E (N)_r ≤ K^r` for every `r ≥ 1` and `K ≥ 1`, then
  `‖N‖_q ≤ 4 (q + 1) K` for every real `q ≥ 1`. The constant depends only on `q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory
open scoped ENNReal

/-- Elementary falling-factorial domination: `n^r ≤ 2^r (n)_r + (2r)^r` for all `n r : ℕ`.
If `n ≥ 2r` then every factor `n - j ≥ n/2`; otherwise `n < 2r`. -/
theorem pow_le_descFactorial (n r : ℕ) :
    n ^ r ≤ 2 ^ r * n.descFactorial r + (2 * r) ^ r := by
  by_cases h : 2 * r ≤ n
  · have h1 : n ≤ 2 * (n + 1 - r) := by omega
    have h2 : n ^ r ≤ (2 * (n + 1 - r)) ^ r := Nat.pow_le_pow_left h1 r
    have h3 : (2 * (n + 1 - r)) ^ r ≤ 2 ^ r * n.descFactorial r := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial n r)
    omega
  · have : n ^ r ≤ (2 * r) ^ r := Nat.pow_le_pow_left (by omega) r
    omega

/-- **Factorial-to-ordinary moment conversion.** Law: any probability measure `μ`. Domain:
`N : Ω → ℕ` measurable and bounded by a deterministic `D`. Hypothesis: for every order
`r ≥ 1`, `E (N)_r ≤ K^r` with `K ≥ 1`. Conclusion: for every real `q ≥ 1`,
`‖N‖_{L^q(μ)} ≤ 4 (q + 1) K`. Uniform in `μ`, `N`, `D`, `K`; the constant depends only on
`q`. -/
theorem count_eLpNorm_le_of_factorial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : Ω → ℕ) (hN : Measurable N) (D : ℕ) (hD : ∀ ω, N ω ≤ D)
    (K : ℝ) (hK : 1 ≤ K)
    (hfac : ∀ r : ℕ, 1 ≤ r → (∫ ω, ((N ω).descFactorial r : ℝ) ∂μ) ≤ K ^ r)
    (q : ℝ) (hq : 1 ≤ q) :
    eLpNorm (fun ω => (N ω : ℝ)) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (4 * (q + 1) * K) := by
  set r : ℕ := ⌈q⌉₊ with hr
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hqr : q ≤ r := Nat.le_ceil q
  have hrq : (r : ℝ) ≤ q + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hmeasR : Measurable (fun ω => (N ω : ℝ)) := measurable_from_nat.comp hN
  have hasm : AEStronglyMeasurable (fun ω => (N ω : ℝ)) μ := hmeasR.aestronglyMeasurable
  -- the `r`-th power moment
  have hpow_pt : ∀ ω, ((N ω : ℝ)) ^ r ≤
      2 ^ r * ((N ω).descFactorial r : ℝ) + (2 * r : ℝ) ^ r := by
    intro ω
    exact_mod_cast pow_le_descFactorial (N ω) r
  have hdesc_meas : Measurable (fun ω => ((N ω).descFactorial r : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n.descFactorial r : ℝ))).comp hN
  have hdesc_int : Integrable (fun ω => ((N ω).descFactorial r : ℝ)) μ := by
    refine Integrable.of_bound hdesc_meas.aestronglyMeasurable ((D : ℝ) ^ r)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (N ω).descFactorial r ≤ D ^ r :=
      (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (hD ω) r)
    exact_mod_cast h1
  have hpow_int : Integrable (fun ω => ((N ω : ℝ)) ^ r) μ := by
    refine Integrable.of_bound (hmeasR.pow_const r).aestronglyMeasurable ((D : ℝ) ^ r)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hD ω) r
  have hmom : (∫ ω, ((N ω : ℝ)) ^ r ∂μ) ≤ (4 * r * K) ^ r := by
    calc (∫ ω, ((N ω : ℝ)) ^ r ∂μ)
        ≤ ∫ ω, (2 ^ r * ((N ω).descFactorial r : ℝ) + (2 * r : ℝ) ^ r) ∂μ :=
          integral_mono hpow_int ((hdesc_int.const_mul _).add (integrable_const _)) hpow_pt
      _ = 2 ^ r * (∫ ω, ((N ω).descFactorial r : ℝ) ∂μ) + (2 * r : ℝ) ^ r := by
          rw [integral_add (hdesc_int.const_mul _) (integrable_const _), integral_const_mul]
          simp
      _ ≤ 2 ^ r * K ^ r + (2 * r : ℝ) ^ r := by
          gcongr
          exact hfac r hr1
      _ ≤ (2 * r * K) ^ r + (2 * r * K) ^ r := by
          have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
          have hA : (2 : ℝ) ^ r * K ^ r ≤ (2 * r * K) ^ r := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) (by nlinarith) r
          have hB : (2 * r : ℝ) ^ r ≤ (2 * r * K) ^ r :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) r
          exact add_le_add hA hB
      _ = 2 * (2 * r * K) ^ r := by ring
      _ ≤ 2 ^ r * (2 * r * K) ^ r := by
          gcongr
          calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr1
      _ = (4 * r * K) ^ r := by rw [← mul_pow]; ring
  -- convert to an `L^r` norm
  have hLr : eLpNorm (fun ω => (N ω : ℝ)) (r : ℝ≥0∞) μ ≤ ENNReal.ofReal (4 * r * K) := by
    have hr_ne : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hr1)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr_ne (ENNReal.natCast_ne_top r) hasm]
    simp only [ENNReal.toReal_natCast]
    have hlin : (∫⁻ ω, ‖(N ω : ℝ)‖ₑ ^ (r : ℝ) ∂μ) = ENNReal.ofReal (∫ ω, ((N ω : ℝ)) ^ r ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hpow_int
        (Filter.Eventually.of_forall fun ω => by positivity)]
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0.le, Real.rpow_natCast]
    rw [hlin]
    have hK0 : (0 : ℝ) ≤ 4 * r * K := by positivity
    calc ENNReal.ofReal (∫ ω, ((N ω : ℝ)) ^ r ∂μ) ^ (1 / (r : ℝ))
        ≤ ENNReal.ofReal ((4 * r * K) ^ r) ^ (1 / (r : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (4 * r * K) := by
          rw [ENNReal.ofReal_pow hK0, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          rw [mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
  calc eLpNorm (fun ω => (N ω : ℝ)) (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun ω => (N ω : ℝ)) (r : ℝ≥0∞) μ := by
        apply eLpNorm_le_eLpNorm_of_exponent_le
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hqr
    _ ≤ ENNReal.ofReal (4 * r * K) := hLr
    _ ≤ ENNReal.ofReal (4 * (q + 1) * K) := by
        apply ENNReal.ofReal_le_ofReal
        have : (0 : ℝ) ≤ K := by linarith
        nlinarith

end BlockBand.Window.Count
