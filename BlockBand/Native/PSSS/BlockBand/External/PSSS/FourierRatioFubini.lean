module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioKernelTransform

/-!
# Absolute integrability of the APSSS Fourier kernel

This module proves the Tonelli/Fubini input for APSSS Claim 2.  The oscillatory
Fourier phase has norm one, so absolute integrability reduces to one real Gaussian
integral followed by a Gamma-integrable positive-axis function.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The two-dimensional Fourier integrand of the regularized APSSS heat kernel. -/
def fourierRatioIntegrand (ε δ ξ η : ℝ) (p : ℝ × ℝ) : ℂ :=
  (regularizedFourierRatioKernel ε δ p.1 p.2 : ℂ) *
    Complex.exp (-(I * ((ξ : ℂ) * p.1 + (η : ℂ) * p.2)))

/-- The oscillatory phase in the APSSS kernel has unit norm. -/
theorem norm_fourierRatioIntegrand (ε δ ξ η : ℝ) (p : ℝ × ℝ) :
    ‖fourierRatioIntegrand ε δ ξ η p‖ =
      |regularizedFourierRatioKernel ε δ p.1 p.2| := by
  unfold fourierRatioIntegrand
  rw [norm_mul, Complex.norm_exp]
  have : (-(I * ((ξ : ℂ) * p.1 + (η : ℂ) * p.2))).re = 0 := by
    simp [Complex.mul_re]
  rw [this, Real.exp_zero, mul_one, norm_real, Real.norm_eq_abs]

/-- Exact integral of the absolute value of a transverse Gaussian slice. -/
theorem integral_abs_regularizedFourierRatioKernel_slice {ε δ x : ℝ}
    (hε : 0 < ε) :
    ∫ y : ℝ, |regularizedFourierRatioKernel ε δ x y| =
      if 0 < x then
        2 * Real.sqrt Real.pi * ε * Real.sqrt x * Real.exp (-δ * x) * x ^ δ
      else 0 := by
  by_cases hx : 0 < x
  · rw [ite_eq_left hx]
    have hb : 0 < 1 / (4 * ε ^ 2 * x) := by positivity
    have hnonneg (y : ℝ) :
        0 ≤ regularizedFourierRatioKernel ε δ x y := by
      simp [regularizedFourierRatioKernel, hx]
      positivity
    simp_rw [abs_of_nonneg (hnonneg _)]
    simp_rw [regularizedFourierRatioKernel, hx, ite_true]
    have he (y : ℝ) :
        -y ^ 2 / (4 * ε ^ 2 * x) = -(1 / (4 * ε ^ 2 * x)) * y ^ 2 := by
      field_simp
    simp_rw [he, mul_assoc]
    rw [integral_mul_const, integral_gaussian]
    have hsqrt : Real.sqrt (Real.pi / (1 / (4 * ε ^ 2 * x))) =
        2 * Real.sqrt Real.pi * ε * Real.sqrt x := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      field_simp
      ring_nf
      rw [Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hx.le]
    rw [show 4 * (ε ^ 2 * x) = 4 * ε ^ 2 * x by ring, hsqrt]
    ring
  · rw [ite_eq_right hx]
    simp [regularizedFourierRatioKernel, hx]

/-- The outer norm integral after evaluating the transverse Gaussian slice is
integrable for every positive regularizer. -/
theorem integrable_fourierRatio_norm_slice {ε δ : ℝ}
    (_hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (fun x : ℝ =>
      if 0 < x then
        2 * Real.sqrt Real.pi * ε * Real.sqrt x * Real.exp (-δ * x) * x ^ δ
      else 0) := by
  let C : ℝ := 2 * Real.sqrt Real.pi * ε
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ (δ + 1 / 2) * Real.exp (-δ * x)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := δ + 1 / 2) (b := δ)
      (by linarith) (by norm_num) hδ using 1
    funext x
    congr 2
    norm_num
  have hCOn : IntegrableOn
      (fun x : ℝ => C * (x ^ (δ + 1 / 2) * Real.exp (-δ * x))) (Ioi 0) :=
    hbase.const_mul C
  have hC := hCOn.integrable_indicator measurableSet_Ioi
  apply hC.congr
  filter_upwards with x
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi 0 from hx), ite_eq_left hx]
    simp only [C]
    simp_rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_add hx]
    ring
  · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx)]
    simp [hx]

end PSSSNative.BlockBand.PSSS
