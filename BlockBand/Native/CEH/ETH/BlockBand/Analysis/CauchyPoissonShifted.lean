module

public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.CauchyPoisson
public import Mathlib.Probability.Distributions.Cauchy

/-!
# Shifted Cauchy–Poisson averaging

This module proves the full scalar Cauchy convolution identity needed for the
commuting case of the projected-Wegner/passive-log harmonic step.  Unlike the
centered precursor, the Hermitian diagonal entry `x` is arbitrary.  The proof
uses a real partial-fraction decomposition.  Its logarithmic derivative has
zero integral because the associated quotient of quadratics has the same
limit at both ends of the real line.

Finite summation then gives the exact simultaneously diagonalized matrix trace
identity for arbitrary real diagonal `A` and nonnegative diagonal absorber
`Y`, with the ordinary unnormalized trace convention.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace CEHNative.BlockBand

/-- The shifted scalar Poisson kernel is integrable against the standard
Cauchy density. -/
theorem integrable_standardCauchyWeight_mul_shifted_poisson
    (x y : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun t : ℝ => standardCauchyWeight t *
      (η / ((x + y * t) ^ 2 + η ^ 2))) := by
  have hw : Integrable standardCauchyWeight := by
    unfold standardCauchyWeight
    convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
    funext t
    field_simp [Real.pi_ne_zero]
  apply (hw.const_mul η⁻¹).mono'
  · apply Continuous.aestronglyMeasurable
    unfold standardCauchyWeight
    fun_prop (discharger := intro t; positivity)
  · filter_upwards with t
    have hden : 0 < (x + y * t) ^ 2 + η ^ 2 := by positivity
    have hw0 : 0 ≤ standardCauchyWeight t := by
      unfold standardCauchyWeight
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hw0 (div_nonneg hη.le hden.le))]
    rw [show η⁻¹ * standardCauchyWeight t =
      standardCauchyWeight t * η⁻¹ by ring]
    gcongr
    calc
      η / ((x + y * t) ^ 2 + η ^ 2) ≤ η / η ^ 2 := by
        apply div_le_div_of_nonneg_left hη.le (sq_pos_of_pos hη)
        nlinarith [sq_nonneg (x + y * t)]
      _ = η⁻¹ := by field_simp

/-- Integral and integrability of a translated Poisson denominator. -/
theorem integral_inv_shifted_sq_add_sq
    (x : ℝ) {η y : ℝ} (hη : 0 < η) (hy : 0 < y) :
    Integrable (fun t : ℝ => ((x + y * t) ^ 2 + η ^ 2)⁻¹) ∧
      (∫ t : ℝ, ((x + y * t) ^ 2 + η ^ 2)⁻¹) =
        Real.pi / (η * y) := by
  let γ : ℝ≥0 := ⟨η / y, (div_pos hη hy).le⟩
  have hγ : γ ≠ 0 := by
    have : 0 < γ := div_pos hη hy
    exact this.ne'
  have hfun : (fun t : ℝ => ((x + y * t) ^ 2 + η ^ 2)⁻¹) =
      fun t => (Real.pi / (η * y)) *
        ProbabilityTheory.cauchyPDFReal (-x / y) γ t := by
    funext t
    rw [ProbabilityTheory.cauchyPDFReal_def]
    change ((x + y * t) ^ 2 + η ^ 2)⁻¹ =
      (Real.pi / (η * y)) *
        (Real.pi⁻¹ * (η / y) *
          ((t - (-x / y)) ^ 2 + (η / y) ^ 2)⁻¹)
    field_simp [hη.ne', hy.ne', Real.pi_ne_zero]
    ring
  rw [hfun]
  constructor
  · exact (ProbabilityTheory.integrable_cauchyPDFReal (-x / y)).const_mul _
  · rw [integral_const_mul,
      ProbabilityTheory.integral_cauchyPDFReal_eq_one (-x / y) hγ]
    ring

private theorem tendsto_quadratic_ratio
    (x η y : ℝ) (hη : 0 < η) (hy : 0 < y) {l : Filter ℝ}
    (hinv : Filter.Tendsto (fun t : ℝ => t⁻¹) l (nhds 0))
    (hne : ∀ᶠ t in l, t ≠ 0) :
    Filter.Tendsto
      (fun t : ℝ => (1 + t ^ 2) /
        ((x + y * t) ^ 2 + η ^ 2)) l
      (nhds (1 / y ^ 2)) := by
  have hden : ∀ u : ℝ,
      (x * u + y) ^ 2 + η ^ 2 * u ^ 2 ≠ 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu, hy.ne']
    · have : 0 < η ^ 2 * u ^ 2 := by positivity
      nlinarith [sq_nonneg (x * u + y)]
  have hg : Continuous (fun u : ℝ =>
      (u ^ 2 + 1) / ((x * u + y) ^ 2 + η ^ 2 * u ^ 2)) := by
    fun_prop
  have ht := hg.continuousAt.tendsto.comp hinv
  have ht' : Filter.Tendsto (fun t : ℝ =>
      (t⁻¹ ^ 2 + 1) /
        ((x * t⁻¹ + y) ^ 2 + η ^ 2 * t⁻¹ ^ 2)) l
      (nhds (1 / y ^ 2)) := by
    convert ht using 1
    · funext t
      rfl
    · norm_num [hy.ne']
  apply ht'.congr'
  filter_upwards [hne] with t ht0
  field_simp [ht0]

/-- General shifted scalar Cauchy convolution identity.  Cauchy averaging a
Poisson kernel of scale `η` along a nonnegative direction of size `y` adds the
scales, with no restriction on the real shift `x`. -/
theorem integral_standardCauchyWeight_mul_shifted_poisson
    (x : ℝ) {η y : ℝ} (hη : 0 < η) (hy : 0 ≤ y) :
    ∫ t : ℝ, standardCauchyWeight t *
        (η / ((x + y * t) ^ 2 + η ^ 2)) =
      (η + y) / (x ^ 2 + (η + y) ^ 2) := by
  by_cases hx0 : x = 0
  · subst x
    have hc := integral_standardCauchyWeight_mul_centered_poisson hη hy
    convert hc using 1
    · apply integral_congr_ae
      filter_upwards with t
      ring
    · field_simp [ne_of_gt (add_pos_of_pos_of_nonneg hη hy)]
      ring
  by_cases hy0 : y = 0
  · subst y
    rw [show (fun t : ℝ => standardCauchyWeight t *
        (η / ((x + 0 * t) ^ 2 + η ^ 2))) =
        fun t => (η / (x ^ 2 + η ^ 2)) * standardCauchyWeight t by
      funext t
      ring]
    rw [integral_const_mul, integral_standardCauchyWeight]
    ring
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  let K : ℝ := x ^ 2 + η ^ 2 - y ^ 2
  let Δ : ℝ := K ^ 2 + 4 * x ^ 2 * y ^ 2
  let a : ℝ := -2 * η * x * y / Δ
  let b : ℝ := η * K / Δ
  let d : ℝ := η * y ^ 2 * (x ^ 2 - η ^ 2 + y ^ 2) / Δ
  have hΔpos : 0 < Δ := by
    dsimp [Δ]
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    nlinarith [sq_nonneg K, mul_pos hx2 (sq_pos_of_pos hypos)]
  have hΔ : Δ ≠ 0 := hΔpos.ne'
  have hΔnorm :
      η ^ 2 * x ^ 2 * 2 - η ^ 2 * y ^ 2 * 2 + η ^ 4 +
          x ^ 2 * y ^ 2 * 2 + x ^ 4 + y ^ 4 ≠ 0 := by
    convert hΔ using 1
    dsimp [Δ, K]
    ring
  let f : ℝ → ℝ := fun t => standardCauchyWeight t *
    (η / ((x + y * t) ^ 2 + η ^ 2))
  let q : ℝ → ℝ := fun t => (1 + t ^ 2) /
    ((x + y * t) ^ 2 + η ^ 2)
  let g : ℝ → ℝ := fun t => (a / (2 * Real.pi)) * Real.log (q t)
  let g' : ℝ → ℝ := fun t => (a / Real.pi) *
    (t / (1 + t ^ 2) - y * (x + y * t) /
      ((x + y * t) ^ 2 + η ^ 2))
  have hf : Integrable f := by
    exact integrable_standardCauchyWeight_mul_shifted_poisson x y hη
  obtain ⟨hshift, hshiftIntegral⟩ :=
    integral_inv_shifted_sq_add_sq x hη hypos
  have hbase : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hdecomp : f = fun t => g' t +
      (b / Real.pi) * (1 + t ^ 2)⁻¹ +
      (d / Real.pi) * ((x + y * t) ^ 2 + η ^ 2)⁻¹ := by
    funext t
    dsimp [f, g', standardCauchyWeight]
    have h1 : 1 + t ^ 2 ≠ 0 := by positivity
    have h2 : (x + y * t) ^ 2 + η ^ 2 ≠ 0 := by positivity
    field_simp [h1, h2, hΔ, hΔnorm, Real.pi_ne_zero]
    dsimp [a, b, d, Δ, K]
    field_simp [hΔnorm]
    ring
  have hg'int : Integrable g' := by
    rw [hdecomp] at hf
    have hr := (hbase.const_mul (b / Real.pi)).add
      (hshift.const_mul (d / Real.pi))
    exact (hf.sub hr).congr (Filter.Eventually.of_forall fun t => by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring)
  have hgderiv : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : 1 + t ^ 2 ≠ 0 := by positivity
    have h2 : (x + y * t) ^ 2 + η ^ 2 ≠ 0 := by positivity
    have hD1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      convert (hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2) using 1
      · rfl
      · simp
    have hD2 : HasDerivAt (fun s : ℝ => (x + y * s) ^ 2 + η ^ 2)
        (2 * y * (x + y * t)) t := by
      convert ((((hasDerivAt_id t).const_mul y).const_add x).pow 2).const_add (η ^ 2)
        using 1
      · funext s
        simp
        ring
      · simp
        ring
    have hq : HasDerivAt q
        ((2 * t * ((x + y * t) ^ 2 + η ^ 2) -
          (1 + t ^ 2) * (2 * y * (x + y * t))) /
          ((x + y * t) ^ 2 + η ^ 2) ^ 2) t := by
      exact hD1.div hD2 h2
    have hq0 : q t ≠ 0 := div_ne_zero h1 h2
    have hlog := hq.log hq0
    dsimp [g]
    convert hlog.const_mul (a / (2 * Real.pi)) using 1
    dsimp [g', q] at *
    field_simp [h1, h2, Real.pi_ne_zero]
  have hratioTop : Filter.Tendsto q Filter.atTop (nhds (1 / y ^ 2)) := by
    exact tendsto_quadratic_ratio x η y hη hypos tendsto_inv_atTop_zero
      (Filter.eventually_gt_atTop (0 : ℝ) |>.mono fun _ ht => ht.ne')
  have hratioBot : Filter.Tendsto q Filter.atBot (nhds (1 / y ^ 2)) := by
    exact tendsto_quadratic_ratio x η y hη hypos tendsto_inv_atBot_zero
      (Filter.eventually_lt_atBot (0 : ℝ) |>.mono fun _ ht => ht.ne)
  have hlogcont : ContinuousAt Real.log (1 / y ^ 2) :=
    Real.continuousAt_log (by positivity)
  have hgTop : Filter.Tendsto g Filter.atTop
      (nhds ((a / (2 * Real.pi)) * Real.log (1 / y ^ 2))) := by
    exact (hlogcont.tendsto.comp hratioTop).const_mul _
  have hgBot : Filter.Tendsto g Filter.atBot
      (nhds ((a / (2 * Real.pi)) * Real.log (1 / y ^ 2))) := by
    exact (hlogcont.tendsto.comp hratioBot).const_mul _
  have hgIntegral : (∫ t : ℝ, g' t) = 0 := by
    rw [integral_of_hasDerivAt_of_tendsto hgderiv hg'int hgBot hgTop]
    ring
  change (∫ t : ℝ, f t) =
    (η + y) / (x ^ 2 + (η + y) ^ 2)
  rw [hdecomp]
  simp only
  calc
    (∫ t : ℝ, g' t + (b / Real.pi) * (1 + t ^ 2)⁻¹ +
        (d / Real.pi) * ((x + y * t) ^ 2 + η ^ 2)⁻¹) =
        (∫ t : ℝ, g' t + (b / Real.pi) * (1 + t ^ 2)⁻¹) +
          ∫ t : ℝ, (d / Real.pi) *
            ((x + y * t) ^ 2 + η ^ 2)⁻¹ :=
      integral_add (hg'int.add (hbase.const_mul _)) (hshift.const_mul _)
    _ = ((∫ t : ℝ, g' t) +
          ∫ t : ℝ, (b / Real.pi) * (1 + t ^ 2)⁻¹) +
          ∫ t : ℝ, (d / Real.pi) *
            ((x + y * t) ^ 2 + η ^ 2)⁻¹ := by
      rw [integral_add hg'int (hbase.const_mul _)]
    _ = (η + y) / (x ^ 2 + (η + y) ^ 2) := by
      rw [hgIntegral, zero_add, integral_const_mul, integral_const_mul,
        integral_univ_inv_one_add_sq, hshiftIntegral]
      dsimp [a, b, d, Δ, K]
      field_simp [Real.pi_ne_zero, hη.ne', hypos.ne', hΔ]
      ring

/-- Finite commuting/diagonal Poisson identity with arbitrary real diagonal
entries `x` and nonnegative absorber eigenvalues `y`. -/
theorem integral_standardCauchyWeight_mul_sum_shifted_poisson
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) {η : ℝ} (hη : 0 < η)
    (hy : ∀ i, 0 ≤ y i) :
    ∫ t : ℝ, standardCauchyWeight t *
        (∑ i, η / ((x i + y i * t) ^ 2 + η ^ 2)) =
      ∑ i, (η + y i) / (x i ^ 2 + (η + y i) ^ 2) := by
  rw [show (fun t : ℝ => standardCauchyWeight t *
      (∑ i, η / ((x i + y i * t) ^ 2 + η ^ 2))) =
      fun t => ∑ i, standardCauchyWeight t *
        (η / ((x i + y i * t) ^ 2 + η ^ 2)) by
    funext t
    rw [Finset.mul_sum]]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_standardCauchyWeight_mul_shifted_poisson (x i) (y i) hη)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact integral_standardCauchyWeight_mul_shifted_poisson (x i) hη (hy i)

/-- Negative-imaginary resolvent form of the finite commuting/diagonal
identity.  This is exactly the PSSS Poisson step after simultaneous unitary
diagonalization of the Hermitian real part and the absorber. -/
theorem integral_standardCauchyWeight_mul_sum_shifted_neg_im_resolvent
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) {η : ℝ} (hη : 0 < η)
    (hy : ∀ i, 0 ≤ y i) :
    ∫ t : ℝ, standardCauchyWeight t *
        (∑ i, -((((x i + y i * t : ℝ) : ℂ) + Complex.I * η)⁻¹).im) =
      ∑ i, -((((x i : ℝ) : ℂ) + Complex.I * (η + y i))⁻¹).im := by
  have hrhs :
      (∑ i, -((((x i : ℝ) : ℂ) + Complex.I * (η + y i))⁻¹).im) =
        ∑ i, (η + y i) / (x i ^ 2 + (η + y i) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _hi
    convert neg_im_inv_ofReal_add_I_mul (x i) (η + y i) using 1
    norm_num
  rw [hrhs]
  simp_rw [neg_im_inv_ofReal_add_I_mul]
  exact integral_standardCauchyWeight_mul_sum_shifted_poisson x y hη hy

end CEHNative.BlockBand
