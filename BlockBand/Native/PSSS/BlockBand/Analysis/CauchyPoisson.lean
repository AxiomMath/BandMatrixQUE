module

public import BlockBand.Native.PSSS.BlockBand.Analysis.PositiveResolvent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A centered Cauchy–Poisson averaging identity

This module proves a scalar harmonic-averaging calculation used in the
projected Wegner and passive-log arguments.  Mathlib supplies the mass of the
Cauchy kernel, but not its convolution semigroup law.  We prove the centered
case directly by partial fractions and then commute the integral with a finite
spectral sum.

The result is the exact specialization of the desired absorbed-resolvent
identity to a commuting absorber with zero Hermitian real part.  The
coincident-scale case, where partial-fraction coefficients are singular, is
proved separately from an elementary antiderivative.  The noncommuting matrix
identity is proved separately, by a mean-value argument on the upper
half-plane.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace PSSSNative.BlockBand

/-- The standard Cauchy probability density `1 / (π (1 + t²))`. -/
def standardCauchyWeight (t : ℝ) : ℝ :=
  1 / (Real.pi * (1 + t ^ 2))

/-- The standard Cauchy weight has total mass one. -/
theorem integral_standardCauchyWeight :
    ∫ t : ℝ, standardCauchyWeight t = 1 := by
  unfold standardCauchyWeight
  rw [show (fun t : ℝ => 1 / (Real.pi * (1 + t ^ 2))) =
      fun t => Real.pi⁻¹ * (1 + t ^ 2)⁻¹ by
    funext t
    field_simp]
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  field_simp [Real.pi_ne_zero]

private theorem tendsto_self_div_one_add_sq_atTop :
    Filter.Tendsto (fun x : ℝ => x / (1 + x ^ 2))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' (a := fun x : ℝ => 1 / x) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x / (1 + x ^ 2))]
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + x ^ 2) hx0]
    nlinarith
  · exact tendsto_const_nhds.div_atTop Filter.tendsto_id

private theorem tendsto_self_div_one_add_sq_atBot :
    Filter.Tendsto (fun x : ℝ => x / (1 + x ^ 2))
      Filter.atBot (nhds 0) := by
  have h := tendsto_self_div_one_add_sq_atTop.comp
    (Filter.tendsto_neg_atBot_atTop : Filter.Tendsto
      (fun x : ℝ => -x) Filter.atBot Filter.atTop)
  convert h.neg using 1
  · funext x
    change x / (1 + x ^ 2) = -((-x) / (1 + (-x) ^ 2))
    ring_nf
  · simp

/-- The elementary squared Cauchy kernel has mass `π / 2`.  This is the
coincident-scale case omitted by the partial-fraction denominators below. -/
theorem integral_inv_one_add_sq_sq :
    ∫ t : ℝ, (1 + t ^ 2)⁻¹ ^ 2 = Real.pi / 2 := by
  have hi : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ ^ 2) := by
    apply integrable_inv_one_add_sq.mono'
    · fun_prop (discharger := intro x; positivity)
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hnonneg : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
      have hle : (1 + t ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity : 0 < 1 + t ^ 2)]
        nlinarith [sq_nonneg t]
      nlinarith
  let F : ℝ → ℝ := fun t =>
    (Real.arctan t + t / (1 + t ^ 2)) / 2
  have hderiv : ∀ t, HasDerivAt F ((1 + t ^ 2)⁻¹ ^ 2) t := by
    intro t
    have hden : 1 + t ^ 2 ≠ 0 := by positivity
    have hquot := (hasDerivAt_id t).div
      ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) hden
    have hquot' : HasDerivAt (fun x : ℝ => x / (1 + x ^ 2))
        ((1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
      convert hquot using 1
      · rfl
      · simp
        ring
    change HasDerivAt
      (fun t : ℝ => (Real.arctan t + t / (1 + t ^ 2)) / 2)
      ((1 + t ^ 2)⁻¹ ^ 2) t
    convert ((Real.hasDerivAt_arctan t).add hquot').div_const 2 using 1
    field_simp [hden]
    ring_nf
  have htop : Filter.Tendsto F Filter.atTop
      (nhds (Real.pi / 4)) := by
    dsimp [F]
    convert (Filter.Tendsto.add
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop)
      tendsto_self_div_one_add_sq_atTop).div_const 2 using 1
    ring_nf
  have hbot : Filter.Tendsto F Filter.atBot
      (nhds (-Real.pi / 4)) := by
    dsimp [F]
    convert (Filter.Tendsto.add
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot)
      tendsto_self_div_one_add_sq_atBot).div_const 2 using 1
    ring_nf
  convert integral_of_hasDerivAt_of_tendsto hderiv hi hbot htop using 1
  ring

end PSSSNative.BlockBand
