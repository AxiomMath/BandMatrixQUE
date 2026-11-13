module

public import BlockBand.Coarea.Native.BlockBand.Analysis.PositiveResolvent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A centered Cauchy–Poisson averaging identity

This module isolates a scalar harmonic-averaging calculation needed by
projected Wegner and passive-log arguments.  Mathlib supplies the mass of the
Cauchy kernel, but not its convolution semigroup law.  We prove the centered
case directly by partial fractions and then commute the integral with a finite
spectral sum.

The result is the exact specialization of the desired absorbed-resolvent
identity to a commuting absorber with zero Hermitian real part.  The
coincident-scale case, where partial-fraction coefficients are singular, is
proved separately from an elementary antiderivative.  The fully noncommuting
matrix identity additionally requires an operator-valued Poisson/Cauchy
transform theorem, which is not presently available in Mathlib.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace CoareaNative.BlockBand

/-- The standard Cauchy probability density, written in the paper's
normalization. -/
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

/-- Scaling formula for a centered Poisson denominator. -/
theorem integral_inv_add_mul_sq
    {η y : ℝ} (hη : 0 < η) (hy : 0 < y) :
    ∫ t : ℝ, (η ^ 2 + (y * t) ^ 2)⁻¹ = Real.pi / (η * y) := by
  have hb : y / η ≠ 0 := div_ne_zero hy.ne' hη.ne'
  have h := integral_univ_inv_one_add_mul_sq (y / η)
  rw [show (fun t : ℝ => (η ^ 2 + (y * t) ^ 2)⁻¹) =
      fun t => (η ^ 2)⁻¹ * (1 + ((y / η) * t) ^ 2)⁻¹ by
    funext t
    field_simp [hη.ne']]
  rw [integral_const_mul, h]
  rw [abs_of_pos (div_pos hy hη)]
  field_simp [hη.ne', hy.ne']

/-- The centered Cauchy–Poisson integrand is integrable for every real
absorber parameter once the regulator is positive. -/
theorem integrable_standardCauchyWeight_mul_centered_poisson
    {η y : ℝ} (hη : 0 < η) :
    Integrable (fun t : ℝ => standardCauchyWeight t *
      (η / ((y * t) ^ 2 + η ^ 2))) := by
  have hw : Integrable standardCauchyWeight := by
    unfold standardCauchyWeight
    convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
    funext t
    field_simp [Real.pi_ne_zero]
  apply (hw.const_mul η⁻¹).mono'
  · apply Continuous.aestronglyMeasurable
    unfold standardCauchyWeight
    fun_prop (discharger := intro x; positivity)
  · filter_upwards with t
    have hden : 0 < (y * t) ^ 2 + η ^ 2 := by positivity
    have hw_nonneg : 0 ≤ standardCauchyWeight t := by
      unfold standardCauchyWeight
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hw_nonneg (div_nonneg hη.le hden.le))]
    rw [show η⁻¹ * standardCauchyWeight t =
      standardCauchyWeight t * η⁻¹ by ring]
    gcongr
    calc
      η / ((y * t) ^ 2 + η ^ 2) ≤ η / η ^ 2 := by
        apply div_le_div_of_nonneg_left hη.le (sq_pos_of_pos hη)
        nlinarith [sq_nonneg (y * t)]
      _ = η⁻¹ := by field_simp

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

/-- Centered scalar Cauchy–Poisson identity.  For positive regulator `η` and
nonnegative absorber eigenvalue `y`, Cauchy averaging adds the scale `y` to
`η`. -/
theorem integral_standardCauchyWeight_mul_centered_poisson
    {η y : ℝ} (hη : 0 < η) (hy : 0 ≤ y) :
    ∫ t : ℝ, standardCauchyWeight t *
        (η / ((y * t) ^ 2 + η ^ 2)) =
      1 / (η + y) := by
  by_cases hy0 : y = 0
  · subst y
    have hη0 : η ≠ 0 := hη.ne'
    rw [show (fun t : ℝ => standardCauchyWeight t *
        (η / ((0 * t) ^ 2 + η ^ 2))) =
        fun t => η⁻¹ * standardCauchyWeight t by
      funext t
      field_simp
      ring]
    rw [integral_const_mul, integral_standardCauchyWeight]
    field_simp
    simp
  by_cases hyeq : y = η
  · subst y
    rw [show (fun t : ℝ => standardCauchyWeight t *
        (η / ((η * t) ^ 2 + η ^ 2))) =
        fun t => (1 / (Real.pi * η)) * (1 + t ^ 2)⁻¹ ^ 2 by
      funext t
      unfold standardCauchyWeight
      field_simp [hη.ne', Real.pi_ne_zero]
      ring]
    rw [integral_const_mul, integral_inv_one_add_sq_sq]
    field_simp [hη.ne', Real.pi_ne_zero]
    norm_num
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hdiff : η ^ 2 - y ^ 2 ≠ 0 := by
    intro heq
    have : η = y := by nlinarith
    exact hyeq this.symm
  have hscaled : Integrable (fun t : ℝ => (η ^ 2 + (y * t) ^ 2)⁻¹) := by
    have hb : y / η ≠ 0 := div_ne_zero hypos.ne' hη.ne'
    have hi := integrable_inv_one_add_mul_sq hb
    have hc := hi.const_mul ((η ^ 2)⁻¹)
    convert hc using 1
    funext t
    field_simp [hη.ne']
  have hbase : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  rw [show (fun t : ℝ => standardCauchyWeight t *
      (η / ((y * t) ^ 2 + η ^ 2))) =
      fun t => (η / (Real.pi * (η ^ 2 - y ^ 2))) * (1 + t ^ 2)⁻¹ -
        (η * y ^ 2 / (Real.pi * (η ^ 2 - y ^ 2))) *
          (η ^ 2 + (y * t) ^ 2)⁻¹ by
    funext t
    unfold standardCauchyWeight
    have h1 : 1 + t ^ 2 ≠ 0 := by positivity
    have h2 : (y * t) ^ 2 + η ^ 2 ≠ 0 := by positivity
    field_simp [h1, h2, hdiff, Real.pi_ne_zero]
    ring]
  rw [integral_sub (hbase.const_mul _) (hscaled.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_univ_inv_one_add_sq, integral_inv_add_mul_sq hη hypos]
  field_simp [Real.pi_ne_zero, hη.ne', hypos.ne', hdiff]
  ring

/-- Negative imaginary part of a scalar resolvent, in Poisson-kernel form. -/
theorem neg_im_inv_ofReal_add_I_mul (x η : ℝ) :
    -(((x : ℂ) + Complex.I * η)⁻¹).im =
      η / (x ^ 2 + η ^ 2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  ring

/-- Finite commuting spectral version of the centered Cauchy–Poisson
identity.  This is the trace formula after simultaneous diagonalization in
the special case where the Hermitian real part is zero. -/
theorem integral_standardCauchyWeight_mul_sum_centered_poisson
    {ι : Type*} [Fintype ι]
    {η : ℝ} (hη : 0 < η) (y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    ∫ t : ℝ, standardCauchyWeight t *
        (∑ i, η / ((y i * t) ^ 2 + η ^ 2)) =
      ∑ i, 1 / (η + y i) := by
  rw [show (fun t : ℝ => standardCauchyWeight t *
      (∑ i, η / ((y i * t) ^ 2 + η ^ 2))) =
      fun t => ∑ i, standardCauchyWeight t *
        (η / ((y i * t) ^ 2 + η ^ 2)) by
    funext t
    rw [Finset.mul_sum]]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_standardCauchyWeight_mul_centered_poisson hη)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact integral_standardCauchyWeight_mul_centered_poisson hη (hy i)

/-- Resolvent notation for the finite commuting specialization.  Each summand
is the negative imaginary part of a scalar diagonal resolvent; hence the
finite sum is the ordinary trace after diagonalization. -/
theorem integral_standardCauchyWeight_mul_sum_neg_im_resolvent
    {ι : Type*} [Fintype ι]
    {η : ℝ} (hη : 0 < η) (y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    ∫ t : ℝ, standardCauchyWeight t *
        (∑ i, -((((y i * t : ℝ) : ℂ) + Complex.I * η)⁻¹).im) =
      ∑ i, -((((0 : ℝ) : ℂ) + Complex.I * (η + y i))⁻¹).im := by
  have hrhs :
      (∑ i, -((((0 : ℝ) : ℂ) + Complex.I * (η + y i))⁻¹).im) =
        ∑ i, 1 / (η + y i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    convert neg_im_inv_ofReal_add_I_mul 0 (η + y i) using 1 <;> norm_num
    field_simp [ne_of_gt (add_pos_of_pos_of_nonneg hη (hy i))]
  rw [hrhs]
  simp_rw [neg_im_inv_ofReal_add_I_mul]
  exact integral_standardCauchyWeight_mul_sum_centered_poisson hη y hy

end CoareaNative.BlockBand
