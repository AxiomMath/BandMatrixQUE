module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Angle-integral lemmas for the radial Gaussian comparison (package K-B′)

One-dimensional facts about integrals over the angle:

* `gc_integral_two_pi_eq` : `∫_0^{2π} f = 2 ∫_0^π f` when `f(2π - x) = f(x)`;
* `gc_integral_Ioo_neg_pi_eq` : `∫_{(-π,π)} f = 2 ∫_{(0,π)} f` when `f` is even;
* `gc_integral_cos_half_ge` : `(1/4) ∫_0^π w ≤ ∫_0^π cos(x/2) w(x)` for continuous `w ≥ 0` with
  `w(π - x) ≤ w(x)` on `[0, π/2]` (fold at `π/2`; `cos(x/2) ≥ 1/2` there);
* `gc_integral_doubling` : `∫_0^π e^{-μ(1 - cos x)} ≤ 2 ∫_0^π e^{-2μ(1 - cos x)}` for `μ ≥ 0`
  (from `2(1 - cos(x/2)) ≤ 1 - cos x` and the substitution `x = 2η`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Real

theorem gc_integral_two_pi_eq {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ x, f (2 * π - x) = f x) :
    ∫ x in (0 : ℝ)..(2 * π), f x = 2 * ∫ x in (0 : ℝ)..π, f x := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hii 0 π) (hii π (2 * π))
  have h2 : ∫ x in π..(2 * π), f x = ∫ x in (0 : ℝ)..π, f x := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) f (2 * π)
    simp only [hs] at this
    rw [this]
    congr 1 <;> ring
  rw [← h1, h2]
  ring

theorem gc_integral_Ioo_neg_pi_eq {f : ℝ → ℝ} (hf : Continuous f) (hs : ∀ x, f (-x) = f x) :
    ∫ x in Ioo (-π) π, f x = 2 * ∫ x in Ioo 0 π, f x := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-π) 0) (hii 0 π)]
  have : ∫ x in (-π)..0, f x = ∫ x in (0 : ℝ)..π, f x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π) f
    simp only [hs, neg_zero] at this
    exact this.symm
  rw [this]
  ring

/-- Folding `[0, π]` at `π / 2`. -/
theorem gc_integral_fold {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x in (0 : ℝ)..π, f x = ∫ x in (0 : ℝ)..(π / 2), (f x + f (π - x)) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hf2 : Continuous fun x => f (π - x) := hf.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_add (hii _ _) (hf2.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) f π
  rw [h, show π - π / 2 = π / 2 by ring, sub_zero,
    intervalIntegral.integral_add_adjacent_intervals (hii 0 (π / 2)) (hii (π / 2) π)]

theorem gc_cos_half_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 2) : 1 / 2 ≤ Real.cos (x / 2) := by
  rw [← Real.cos_pi_div_three]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  linarith [Real.pi_pos]

/-- The `cos(x/2)`-weighted angle integral controls the plain one. -/
theorem gc_integral_cos_half_ge {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hsym : ∀ x ∈ Icc 0 (π / 2), w (π - x) ≤ w x) :
    1 / 4 * ∫ x in (0 : ℝ)..π, w x ≤ ∫ x in (0 : ℝ)..π, Real.cos (x / 2) * w x := by
  have hc : Continuous fun x => Real.cos (x / 2) * w x :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).mul hw
  rw [gc_integral_fold hw, gc_integral_fold hc, ← intervalIntegral.integral_const_mul]
  have hpi := Real.pi_pos
  have hw2 : Continuous fun x => 1 / 4 * (w x + w (π - x)) :=
    continuous_const.mul (hw.add (hw.comp (continuous_const.sub continuous_id)))
  refine intervalIntegral.integral_mono_on (by linarith) (hw2.intervalIntegrable _ _)
    ((hc.add (hc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _) ?_
  intro x hx
  have h1 := gc_cos_half_ge hx.1 hx.2
  have h2 : 0 ≤ Real.cos ((π - x) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h3 := hsym x hx
  have h4 := hw0 x
  have h5 := hw0 (π - x)
  nlinarith [mul_nonneg h2 h5]

theorem gc_one_sub_cos_half_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ π) :
    2 * (1 - Real.cos (x / 2)) ≤ 1 - Real.cos x := by
  have h := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have hc0 : 0 ≤ Real.cos (x / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc1 : Real.cos (x / 2) ≤ 1 := Real.cos_le_one _
  nlinarith [mul_nonneg hc0 (sub_nonneg.2 hc1)]

/-- The angular doubling inequality. -/
theorem gc_integral_doubling {μ : ℝ} (hμ : 0 ≤ μ) :
    ∫ x in (0 : ℝ)..π, Real.exp (-(μ * (1 - Real.cos x))) ≤
      2 * ∫ x in (0 : ℝ)..π, Real.exp (-(2 * μ * (1 - Real.cos x))) := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun x => Real.exp (-(2 * μ * (1 - Real.cos x))) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have h1 : ∫ x in (0 : ℝ)..π, Real.exp (-(μ * (1 - Real.cos x))) ≤
      ∫ x in (0 : ℝ)..π, g (x / 2) := by
    have hc1 : Continuous fun x : ℝ => Real.exp (-(μ * (1 - Real.cos x))) := by fun_prop
    refine intervalIntegral.integral_mono_on hpi.le (hc1.intervalIntegrable _ _)
      ((hgc.comp (continuous_id.div_const 2)).intervalIntegrable _ _) ?_
    intro x hx
    simp only [hg]
    apply Real.exp_le_exp.2
    have := gc_one_sub_cos_half_le x hx.1 hx.2
    nlinarith
  have h2 : ∫ x in (0 : ℝ)..π, g (x / 2) = 2 * ∫ x in (0 : ℝ)..(π / 2), g x := by
    rw [intervalIntegral.integral_comp_div (f := g) (by norm_num : (2 : ℝ) ≠ 0), zero_div,
      smul_eq_mul]
  have h3 : ∫ x in (0 : ℝ)..(π / 2), g x ≤ ∫ x in (0 : ℝ)..π, g x :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (ae_of_all _ fun x => (Real.exp_pos _).le) (hgc.intervalIntegrable _ _)
  have : ∫ x in (0 : ℝ)..π, Real.exp (-(2 * μ * (1 - Real.cos x))) = ∫ x in (0 : ℝ)..π, g x :=
    rfl
  rw [this]
  linarith

end BlockBand.Diffusion
