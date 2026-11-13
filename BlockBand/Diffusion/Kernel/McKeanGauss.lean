module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shifted Gaussian moments

Elementary Gaussian integrals used for the normalisation of McKean's kernel (`T > 0`, Lebesgue
measure on `ℝ`):

* `mk_integral_gauss_shift`: `∫_ℝ s e^{bs - s²/(4T)} ds = 2bT √(4πT) e^{b²T}`;
* `mk_integral_gauss_sinh`: `∫_ℝ s sinh(s/2) e^{-s²/(4T)} ds = T √(4πT) e^{T/4}`;
* `mk_integral_Ioi_gauss_sinh`: the same over `(0, ∞)` is half of it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

theorem mk_gauss_shift_eq {T : ℝ} (hT : 0 < T) (b s : ℝ) :
    s * Real.exp (b * s - s ^ 2 / (4 * T)) = Real.exp (b ^ 2 * T) *
      ((s - 2 * b * T) * Real.exp (-(1 / (4 * T)) * (s - 2 * b * T) ^ 2) +
        2 * b * T * Real.exp (-(1 / (4 * T)) * (s - 2 * b * T) ^ 2)) := by
  have : Real.exp (b * s - s ^ 2 / (4 * T)) =
      Real.exp (b ^ 2 * T) * Real.exp (-(1 / (4 * T)) * (s - 2 * b * T) ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [this]; ring

theorem mk_integrable_gauss_shift {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Integrable fun s : ℝ => s * Real.exp (b * s - s ^ 2 / (4 * T)) := by
  have hc : 0 < 1 / (4 * T) := by positivity
  have h1 := (integrable_mul_exp_neg_mul_sq hc).comp_sub_right (2 * b * T)
  have h2 := ((integrable_exp_neg_mul_sq hc).comp_sub_right (2 * b * T)).const_mul (2 * b * T)
  refine ((h1.add h2).const_mul (Real.exp (b ^ 2 * T))).congr (ae_of_all _ fun s => ?_)
  exact (mk_gauss_shift_eq hT b s).symm

theorem mk_integral_gauss_shift {T : ℝ} (hT : 0 < T) (b : ℝ) :
    ∫ s : ℝ, s * Real.exp (b * s - s ^ 2 / (4 * T)) =
      2 * b * T * Real.sqrt (4 * π * T) * Real.exp (b ^ 2 * T) := by
  have hc : 0 < 1 / (4 * T) := by positivity
  simp_rw [mk_gauss_shift_eq hT b]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun u => u * Real.exp (-(1 / (4 * T)) * u ^ 2) +
    2 * b * T * Real.exp (-(1 / (4 * T)) * u ^ 2)) (2 * b * T)]
  rw [integral_add (integrable_mul_exp_neg_mul_sq hc)
    ((integrable_exp_neg_mul_sq hc).const_mul _), integral_const_mul, integral_gaussian]
  have hodd : ∫ u : ℝ, u * Real.exp (-(1 / (4 * T)) * u ^ 2) = 0 := by
    have h := integral_neg_eq_self (fun u : ℝ => u * Real.exp (-(1 / (4 * T)) * u ^ 2)) volume
    simp only [neg_mul, even_two, Even.neg_pow, integral_neg] at h ⊢
    linarith
  rw [hodd]
  have : π / (1 / (4 * T)) = 4 * π * T := by field_simp
  rw [this]; ring

theorem mk_gauss_sinh_eq {T : ℝ} (s : ℝ) :
    s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)) =
      (1 / 2) * (s * Real.exp ((1 / 2) * s - s ^ 2 / (4 * T)) -
        s * Real.exp ((-1 / 2) * s - s ^ 2 / (4 * T))) := by
  rw [show (1 / 2 : ℝ) * s - s ^ 2 / (4 * T) = s / 2 + -s ^ 2 / (4 * T) by ring,
    show (-1 / 2 : ℝ) * s - s ^ 2 / (4 * T) = -(s / 2) + -s ^ 2 / (4 * T) by ring,
    Real.exp_add, Real.exp_add, Real.sinh_eq]
  ring

theorem mk_integrable_gauss_sinh {T : ℝ} (hT : 0 < T) :
    Integrable fun s : ℝ => s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)) := by
  simp_rw [mk_gauss_sinh_eq]
  exact ((mk_integrable_gauss_shift hT _).sub (mk_integrable_gauss_shift hT _)).const_mul _

theorem mk_integral_gauss_sinh {T : ℝ} (hT : 0 < T) :
    ∫ s : ℝ, s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)) =
      T * Real.sqrt (4 * π * T) * Real.exp (T / 4) := by
  simp_rw [mk_gauss_sinh_eq]
  rw [integral_const_mul, integral_sub (mk_integrable_gauss_shift hT _)
    (mk_integrable_gauss_shift hT _), mk_integral_gauss_shift hT, mk_integral_gauss_shift hT]
  have h1 : (1 / 2 : ℝ) ^ 2 * T = T / 4 := by ring
  have h2 : (-1 / 2 : ℝ) ^ 2 * T = T / 4 := by ring
  rw [h1, h2]; ring

theorem mk_integral_Ioi_gauss_sinh {T : ℝ} (hT : 0 < T) :
    ∫ s in Ioi (0 : ℝ), s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)) =
      T * Real.sqrt (4 * π * T) * Real.exp (T / 4) / 2 := by
  set h := fun s : ℝ => s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)) with hh
  have hint := mk_integrable_gauss_sinh hT
  have heven : ∫ s in Iic (0 : ℝ), h s = ∫ s in Ioi (0 : ℝ), h s := by
    have h0 := integral_comp_neg_Ioi (0 : ℝ) h
    rw [neg_zero] at h0
    rw [← h0]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hh, neg_div, Real.sinh_neg, even_two, Even.neg_pow]
    ring
  have := intervalIntegral.integral_Iic_add_Ioi (f := h) (b := 0) hint.integrableOn
    hint.integrableOn
  rw [heven, mk_integral_gauss_sinh hT] at this
  linarith

end BlockBand.Diffusion
