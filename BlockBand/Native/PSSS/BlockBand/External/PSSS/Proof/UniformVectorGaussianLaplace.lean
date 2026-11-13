module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorGaussianRadius
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Basic

/-!
# Gaussian quadratic Laplace transforms

This module proves the scalar quadratic Laplace transform underlying the
complex-spherical small-ball estimate of APSSS (Aizenman–Peled–Schenker–Shamis–Sodin).
The normalization is the real standard
Gaussian `gaussianReal 0 1`, so the factor is exactly `(1 + 2 a)⁻¹ᐟ²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory

/-- The exact quadratic Laplace transform of a variance-one real Gaussian.
This is the atomic product factor needed after orthogonal diagonalization of a realified
complex linear map. -/
theorem integral_exp_neg_mul_sq_gaussianReal (a : ℝ) (ha : 0 ≤ a) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2) ∂gaussianReal 0 1 =
      (1 + 2 * a) ^ (-(1 : ℝ) / 2) := by
  rw [gaussianReal_of_var_ne_zero (μ := 0) (by norm_num)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun _ => gaussianPDF_lt_top) ]
  simp only [smul_eq_mul, toReal_gaussianPDF, gaussianPDFReal]
  have hb : 0 < a + 1 / 2 := by positivity
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hfun : (fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + 1 / 2) * x ^ 2) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  rw [hfun, integral_const_mul, integral_gaussian (a + 1 / 2)]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt2pi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hbase : 0 < 1 + 2 * a := by positivity
  rw [show Real.pi / (a + 1 / 2) =
      (2 * Real.pi) / (1 + 2 * a) by field_simp; ring]
  rw [Real.sqrt_div (by positivity)]
  simp only [Real.sqrt_eq_rpow]
  have hexp : (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) := by ring
  rw [hexp, Real.rpow_neg hbase.le]
  field_simp

/-- The exact finite-product quadratic Laplace transform.  Each coordinate has the
variance-one real Gaussian law and the coefficients are merely nonnegative; zero
coefficients are allowed.  This is the product estimate required after a
spectral reduction. -/
theorem integral_exp_neg_sum_mul_sq_pi_gaussianReal
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∫ x : ι → ℝ, Real.exp (-∑ i, a i * (x i) ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
        ∏ i, (1 + 2 * a i) ^ (-(1 : ℝ) / 2) := by
  have hfun : (fun x : ι → ℝ => Real.exp (-∑ i, a i * (x i) ^ 2)) =
      fun x => ∏ i, Real.exp (-a i * (x i) ^ 2) := by
    funext x
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [neg_mul]
  rw [hfun]
  calc
    _ = ∏ i, ∫ x : ℝ, Real.exp (-a i * x ^ 2) ∂gaussianReal 0 1 :=
      MeasureTheory.integral_fintype_prod_eq_prod
        (fun i (x : ℝ) => Real.exp (-a i * x ^ 2))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_exp_neg_mul_sq_gaussianReal (a i) (ha i)

/-- Parameterized form of the finite-product identity.  It is the exact Laplace-product
formula for a nonnegative diagonal quadratic form in independent variance-one real
Gaussians. -/
theorem integral_exp_neg_mul_sum_mul_sq_pi_gaussianReal
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ x : ι → ℝ, Real.exp (-t * (∑ i, a i * (x i) ^ 2))
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
        ∏ i, (1 + 2 * t * a i) ^ (-(1 : ℝ) / 2) := by
  have h := integral_exp_neg_sum_mul_sq_pi_gaussianReal
    (fun i => t * a i) (fun i => mul_nonneg ht (ha i))
  have hfun : (fun x : ι → ℝ => Real.exp (-t * (∑ i, a i * (x i) ^ 2))) =
      fun x => Real.exp (-∑ i, (t * a i) * (x i) ^ 2) := by
    funext x
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun, h]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  ring

/-- Exact Chernoff-product bound for the lower tail of a diagonal Gaussian quadratic
form.  This is the probability-level output of the Laplace calculation, before the
spectral realification of a complex matrix. -/
theorem pi_gaussianReal_sum_mul_sq_lowerTail_le_laplaceProduct
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (s t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x : ι → ℝ | (∑ i, a i * (x i) ^ 2) ≤ s} ≤
      Real.exp (t * s) * ∏ i, (1 + 2 * t * a i) ^ (-(1 : ℝ) / 2) := by
  let X : (ι → ℝ) → ℝ := fun x => ∑ i, a i * (x i) ^ 2
  have hXnonneg : ∀ x, 0 ≤ X x := fun x => Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (sq_nonneg _)
  have hmeas : AEMeasurable X (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    apply Measurable.aemeasurable
    fun_prop
  have hint : Integrable (fun x => Real.exp (-t * X x))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
      (hXnonneg x))
  have hchernoff := measure_le_le_exp_mul_mgf (μ :=
      Measure.pi (fun _ : ι => gaussianReal 0 1)) (X := X) (t := -t) s
      (neg_nonpos.mpr ht) hint
  rw [show - -t * s = t * s by ring] at hchernoff
  have hmgf : mgf X (Measure.pi (fun _ : ι => gaussianReal 0 1)) (-t) =
      ∏ i, (1 + 2 * t * a i) ^ (-(1 : ℝ) / 2) := by
    rw [mgf]
    change (∫ x : ι → ℝ, Real.exp (-t * (∑ i, a i * (x i) ^ 2))
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = _
    exact integral_exp_neg_mul_sum_mul_sq_pi_gaussianReal a ha t ht
  rw [hmgf] at hchernoff
  exact hchernoff

end PSSSNative.BlockBand.PSSS
