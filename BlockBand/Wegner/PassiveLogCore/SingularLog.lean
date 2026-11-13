module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Deterministic singular-log estimates

This module formalizes the scalar inequalities used to remove the regulator from the singular and
passive logarithms. Normalization: each spectral point contributes
`(1/2) log (1 + a^2 / (λ-e)^2)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Wegner.PassiveLogCore

open scoped BigOperators

/-- One summand of the singular finite logarithm. -/
def singularLogTerm (x a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + a ^ 2 / x ^ 2)

/-- The regulated full-absorber increment at one real spectral point. -/
def regulatedLogIncrement (x η a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((x ^ 2 + (η + a) ^ 2) / (x ^ 2 + η ^ 2))

/-- Simultaneous nonzero rescaling of the spectral displacement and absorber
does not change a singular-log summand. -/
theorem singularLogTerm_mul_left {L x a : ℝ} (hL : L ≠ 0) :
    singularLogTerm (L * x) (L * a) = singularLogTerm x a := by
  unfold singularLogTerm
  have hratio : (L * a) ^ 2 / (L * x) ^ 2 = a ^ 2 / x ^ 2 := by
    by_cases hx : x = 0
    · simp [hx]
    field_simp [hL, hx]
  rw [hratio]

/-- A singular-log summand is nonnegative away from its pole. -/
theorem singularLogTerm_nonneg {x a : ℝ} (hx : x ≠ 0) :
    0 ≤ singularLogTerm x a := by
  unfold singularLogTerm
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have : 0 ≤ a ^ 2 / x ^ 2 := div_nonneg ha2 hx2.le
  linarith

/-- The elementary large-displacement estimate
`(1/2) log (1 + a²/x²) ≤ a²/(2x²)`. -/
theorem singularLogTerm_le_half_mul_sq_div_sq {x a : ℝ} (hx : x ≠ 0) :
    singularLogTerm x a ≤ (1 / 2 : ℝ) * (a ^ 2 / x ^ 2) := by
  unfold singularLogTerm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hq : 0 ≤ a ^ 2 / x ^ 2 := div_nonneg (sq_nonneg a) hx2.le
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + a ^ 2 / x ^ 2 by
    linarith)
  linarith

/-- Increasing the squared absorber can only increase the singular-log
summand.  This is the pointwise comparison used on dyadic shells. -/
theorem singularLogTerm_mono_sq {x a b : ℝ} (hx : x ≠ 0)
    (hab : a ^ 2 ≤ b ^ 2) :
    singularLogTerm x a ≤ singularLogTerm x b := by
  unfold singularLogTerm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hq : 0 ≤ a ^ 2 / x ^ 2 := div_nonneg (sq_nonneg a) hx2.le
    linarith
  · gcongr

/-- Moving a spectral point away from the pole decreases its singular-log
contribution.  This is the interval form used for dyadic annuli. -/
theorem singularLogTerm_le_of_le_abs {x a δ : ℝ}
    (hδ : 0 < δ) (hx : δ ≤ |x|) :
    singularLogTerm x a ≤ singularLogTerm δ a := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    rw [abs_zero] at hx
    exact (not_le_of_gt hδ) hx
  have hsq : δ ^ 2 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ hδ.le hx 2
    simpa using this
  unfold singularLogTerm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    have hq : 0 ≤ a ^ 2 / x ^ 2 := div_nonneg (sq_nonneg a) hx2.le
    linarith
  · gcongr

/-- Convenient polynomial tail bound on an annulus `δ ≤ |x|`. -/
theorem singularLogTerm_le_half_mul_sq_div_sq_of_le_abs
    {x a δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) :
    singularLogTerm x a ≤ (1 / 2 : ℝ) * (a ^ 2 / δ ^ 2) :=
  (singularLogTerm_le_of_le_abs hδ hx).trans
    (singularLogTerm_le_half_mul_sq_div_sq hδ.ne')

/-- Algebraic core of the regulator dominator.  For `0 ≤ η ≤ a`, the ratio
with heights `η` and `η+a` is bounded by the singular ratio with height `2a`. -/
theorem regulatedRatio_le_singularRatio {x η a : ℝ}
    (hx : x ≠ 0) (hη : 0 ≤ η) (hηa : η ≤ a) :
    (x ^ 2 + (η + a) ^ 2) / (x ^ 2 + η ^ 2) ≤
      1 + 4 * a ^ 2 / x ^ 2 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hden : 0 < x ^ 2 + η ^ 2 := add_pos_of_pos_of_nonneg hx2 (sq_nonneg η)
  rw [show 1 + 4 * a ^ 2 / x ^ 2 = (x ^ 2 + 4 * a ^ 2) / x ^ 2 by
    field_simp]
  rw [div_le_div_iff₀ hden hx2]
  have ha : 0 ≤ a := hη.trans hηa
  nlinarith [sq_nonneg η, sq_nonneg a, mul_nonneg ha (sub_nonneg.mpr hηa)]

/-- The exact domination used for removing the positive regulator from the
passive log: the regulated increment is bounded by the singular-log
summand with parameter `2a`. -/
theorem regulatedLogIncrement_le_singularLogTerm_two_mul
    {x η a : ℝ} (hx : x ≠ 0) (hη : 0 ≤ η) (hηa : η ≤ a) :
    regulatedLogIncrement x η a ≤ singularLogTerm x (2 * a) := by
  unfold regulatedLogIncrement singularLogTerm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hden : 0 < x ^ 2 + η ^ 2 := add_pos_of_pos_of_nonneg hx2 (sq_nonneg η)
  apply Real.log_le_log
  · exact div_pos (add_pos_of_pos_of_nonneg hx2 (sq_nonneg (η + a))) hden
  · calc
      (x ^ 2 + (η + a) ^ 2) / (x ^ 2 + η ^ 2) ≤
          1 + 4 * a ^ 2 / x ^ 2 := regulatedRatio_le_singularRatio hx hη hηa
      _ = 1 + (2 * a) ^ 2 / x ^ 2 := by ring

/-- Exact Cauchy-resolvent representation of one singular logarithm.
This is the scalar identity behind the passage from projected resolvent bounds
to the finite log statistic. -/
theorem integral_cauchy_eq_singularLogTerm {x a : ℝ} (hx : x ≠ 0) :
    ∫ s in (0 : ℝ)..a, s / (x ^ 2 + s ^ 2) = singularLogTerm x a := by
  let F : ℝ → ℝ := fun s => (1 / 2 : ℝ) * Real.log (x ^ 2 + s ^ 2)
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hderiv : ∀ s, HasDerivAt F (s / (x ^ 2 + s ^ 2)) s := by
    intro s
    have hinner : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * s) s := by
      convert (hasDerivAt_const s (x ^ 2)).add ((hasDerivAt_id s).pow 2) using 1
      · funext t
        simp
      · simp [mul_comm]
    have hlog := hinner.log (ne_of_gt (add_pos_of_pos_of_nonneg hx2 (sq_nonneg s)))
    convert hlog.const_mul (1 / 2 : ℝ) using 1
    field_simp
  have hcont : Continuous (fun s : ℝ => s / (x ^ 2 + s ^ 2)) := by
    apply Continuous.div continuous_id (continuous_const.add (continuous_id.pow 2))
    intro s
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx2 (sq_nonneg s))
  have hFTC : ∫ s in (0 : ℝ)..a, s / (x ^ 2 + s ^ 2) = F a - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _hs
      exact hderiv s
    · exact hcont.intervalIntegrable 0 a
  rw [hFTC]
  unfold F singularLogTerm
  have hx2ne : x ^ 2 ≠ 0 := ne_of_gt hx2
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
  rw [show (1 / 2 : ℝ) * Real.log (x ^ 2 + a ^ 2) -
      (1 / 2 : ℝ) * Real.log (x ^ 2) =
      (1 / 2 : ℝ) * (Real.log (x ^ 2 + a ^ 2) - Real.log (x ^ 2)) by ring]
  rw [← Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg hx2 (sq_nonneg a))) hx2ne]
  congr 2
  field_simp

/-- The singular finite log statistic of a finite real spectrum. -/
def singularLogStatistic {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (e a : ℝ) : ℝ :=
  ∑ i, singularLogTerm (eig i - e) a

/-- The rescaling `u = L(λ-e)`: only the product `aL`
remains in the finite statistic. -/
theorem singularLogStatistic_rescale
    {ι : Type*} [Fintype ι] (eig : ι → ℝ) (e a L : ℝ) (hL : L ≠ 0) :
    singularLogStatistic eig e a =
      ∑ i, singularLogTerm (L * (eig i - e)) (L * a) := by
  unfold singularLogStatistic
  apply Finset.sum_congr rfl
  intro i _hi
  exact (singularLogTerm_mul_left hL).symm

/-- Finite spectral form of the Cauchy-resolvent representation.  The
fixed-energy pole exclusion is an explicit hypothesis. -/
theorem integral_cauchy_sum_eq_singularLogStatistic
    {ι : Type*} [Fintype ι] (eig : ι → ℝ) (e a : ℝ)
    (hpole : ∀ i, eig i ≠ e) :
    ∫ s in (0 : ℝ)..a, ∑ i, s / ((eig i - e) ^ 2 + s ^ 2) =
      singularLogStatistic eig e a := by
  rw [intervalIntegral.integral_finsetSum]
  · unfold singularLogStatistic
    apply Finset.sum_congr rfl
    intro i _hi
    exact integral_cauchy_eq_singularLogTerm (sub_ne_zero.mpr (hpole i))
  · intro i _hi
    have hx2 : 0 < (eig i - e) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (hpole i))
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_id (continuous_const.add (continuous_id.pow 2))
    intro s
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx2 (sq_nonneg s))

/-- Termwise regulator domination for a finite spectrum avoiding the fixed
energy. -/
theorem sum_regulatedLogIncrement_le_singularLogStatistic_two_mul
    {ι : Type*} [Fintype ι] (eig : ι → ℝ) (e η a : ℝ)
    (hpole : ∀ i, eig i ≠ e) (hη : 0 ≤ η) (hηa : η ≤ a) :
    ∑ i, regulatedLogIncrement (eig i - e) η a ≤
      singularLogStatistic eig e (2 * a) := by
  unfold singularLogStatistic
  apply Finset.sum_le_sum
  intro i _hi
  apply regulatedLogIncrement_le_singularLogTerm_two_mul
  · exact sub_ne_zero.mpr (hpole i)
  · exact hη
  · exact hηa

end BlockBand.Wegner.PassiveLogCore
