module

public import BlockBand.Window.Transfer.ScalarKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Localization of correlated window expectations

The scalar Gaussian convolution `h` of a window: measurability and uniform bound
`h ≤ 1/(scale σ √(2π))`; pointwise localization by a terminal `L^q` moment plus the Gaussian tail
`exp(-|e-E|²/(32σ²))`; correlated expectation localization
`E[A h(X)] ≤ B min(ε, (2/|e-E|)^q L^q + tail)` for an arbitrary probability measure, measurable
`0 ≤ A ≤ 1` arbitrarily correlated with `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BlockBand.Window.Transfer

noncomputable def scalarKernelPrefactor (scale σ : ℝ) : ℝ :=
  1 / (scale * σ * Real.sqrt (2 * Real.pi))

/-- Measurability of the scalar Gaussian convolution in the energy `x`. -/
theorem measurable_scalarConvolution (w : ℝ → ℝ) (hw : Measurable w)
    (scale E σ : ℝ) : Measurable (scalarConvolution w scale E σ) := by
  have hf : Measurable (fun z : ℝ × ℝ => w (scale * (z.1 + z.2 - E))) :=
    hw.comp (by fun_prop)
  exact hf.stronglyMeasurable.integral_prod_right'
    (ν := gaussianReal 0 (scalarVariance σ)) |>.measurable

/-- The uniform bound `0 ≤ h(x) ≤ 1/(scale σ √(2π))` of the scalar Gaussian convolution, for every
deterministic `x`. -/
theorem scalarConvolution_uniform (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M x : ℝ) (hs : 0 < scale) (hσ : 0 < σ)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    0 ≤ scalarConvolution w scale E σ x ∧
      scalarConvolution w scale E σ x ≤ scalarKernelPrefactor scale σ := by
  have hk := scalar_convolution_bound_continuous w hw hcompact hunit hw0
    scale E σ M x hs hσ hsupp
  have he : Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  refine ⟨hk.2.1, hk.2.2.trans ?_⟩
  exact div_le_div_of_nonneg_right he (by positivity)

/-- Close to the classical rank energy e, the positive-part Gaussian gap is
at least |e-E|/4, once its fixed window width is paid. -/
theorem classical_gap_on_good_event (e E x M scale : ℝ) (_hs : 0 < scale)
    (_hg : 0 < |e - E|) (hwidth : 4 * (M / scale) ≤ |e - E|)
    (hx : |x - e| ≤ |e - E| / 2) :
    |e - E| / 4 ≤ max (|x - E| - M / scale) 0 := by
  have htriangle : |e - E| ≤ |x - e| + |x - E| := by
    simpa only [abs_sub_comm e x] using abs_sub_le e x E
  exact (show |e - E| / 4 ≤ |x - E| - M / scale by linarith).trans (le_max_left _ _)

/-- The Gaussian convolution tail off the rank-deviation event, with variance `σ²` and exponent
`|e - E|²/(32σ²)`. -/
theorem scalarConvolution_good_event (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M e x : ℝ) (hs : 0 < scale) (hσ : 0 < σ)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) (hg : 0 < |e - E|)
    (hwidth : 4 * (M / scale) ≤ |e - E|) (hx : |x - e| ≤ |e - E| / 2) :
    scalarConvolution w scale E σ x ≤ scalarKernelPrefactor scale σ *
      Real.exp (-|e - E| ^ 2 / (32 * σ ^ 2)) := by
  have hk := (scalar_convolution_bound_continuous w hw hcompact hunit hw0
    scale E σ M x hs hσ hsupp).2.2
  have hgap := classical_gap_on_good_event e E x M scale hs hg hwidth hx
  have hgap0 : 0 ≤ max (|x - E| - M / scale) 0 := le_max_right _ _
  have hsq : (|e - E| / 4) ^ 2 ≤ (max (|x - E| - M / scale) 0) ^ 2 := by
    nlinarith [sq_nonneg (max (|x - E| - M / scale) 0 - |e - E| / 4)]
  have hexp : -(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2) ≤
      -|e - E| ^ 2 / (32 * σ ^ 2) := by
    calc
      _ ≤ -(|e - E| / 4) ^ 2 / (2 * σ ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  calc
    _ ≤ Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2)) /
        (scale * σ * Real.sqrt (2 * Real.pi)) := hk
    _ ≤ Real.exp (-|e - E| ^ 2 / (32 * σ ^ 2)) /
        (scale * σ * Real.sqrt (2 * Real.pi)) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by unfold scalarKernelPrefactor; ring

/-- Pointwise localization of the convolution by a terminal moment term plus the Gaussian tail. -/
theorem scalarConvolution_pointwise_localization (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M e x q : ℝ) (hs : 0 < scale) (hσ : 0 < σ) (hq : 0 < q)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) (hg : 0 < |e - E|)
    (hwidth : 4 * (M / scale) ≤ |e - E|) :
    scalarConvolution w scale E σ x ≤ scalarKernelPrefactor scale σ *
      ((2 / |e - E|) ^ q * |x - e| ^ q +
        Real.exp (-|e - E| ^ 2 / (32 * σ ^ 2))) := by
  have hB : 0 ≤ scalarKernelPrefactor scale σ := by unfold scalarKernelPrefactor; positivity
  by_cases hx : |x - e| ≤ |e - E| / 2
  · exact (scalarConvolution_good_event w hw hcompact hunit hw0 scale E σ M e x
      hs hσ hsupp hg hwidth hx).trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) hB)
  · have hratio : 1 ≤ (2 / |e - E|) * |x - e| := by
      have hxgt := lt_of_not_ge hx
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hg).mpr
      nlinarith
    have hpower : 1 ≤ (2 / |e - E|) ^ q * |x - e| ^ q := by
      rw [← Real.mul_rpow (by positivity) (abs_nonneg _)]
      exact Real.one_le_rpow hratio hq.le
    exact (scalarConvolution_uniform w hw hcompact hunit hw0 scale E σ M x
      hs hσ hsupp).2.trans (by nlinarith [Real.exp_nonneg (-|e - E| ^ 2 / (32 * σ ^ 2))])

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A terminal `L^q` bound `‖X - e‖_q ≤ L` (`q > 0`) gives integrability of `|X - e|^q` and
`E|X - e|^q ≤ L^q`. -/
theorem terminal_moment_of_Lq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (_hX : Measurable X) (e q L : ℝ) (hq : 0 < q) (hL : 0 ≤ L)
    (hLp : eLpNorm (fun x => X x - e) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal L) :
    Integrable (fun x => |X x - e| ^ q) μ ∧
      (∫ x, |X x - e| ^ q ∂μ) ≤ L ^ q := by
  have hp0 : ENNReal.ofReal q ≠ 0 := by simp [hq]
  have hm : MemLp (fun x => X x - e) (ENNReal.ofReal q) μ :=
    hLp.trans_lt (by simp)
  have hi : Integrable (fun x => |X x - e| ^ q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using
      hm.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have heq := hm.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] at heq
  rw [heq] at hLp
  have hmoment0 : 0 ≤ ∫ x, |X x - e| ^ q ∂μ := integral_nonneg fun x => by positivity
  have hroot := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hLp
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hmoment0 _), ENNReal.toReal_ofReal hL] at hroot
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hmoment0 _) hroot hq.le
  rw [← Real.rpow_mul hmoment0, inv_mul_cancel₀ hq.ne', Real.rpow_one] at hh
  exact ⟨hi, hh⟩

/-- **Correlated-observable expectation localization**: for measurable `0 ≤ A ≤ 1` with
`E A ≤ ε`, arbitrarily correlated with `X`, and a terminal bound `‖X - e‖_q ≤ L`,
`E[A h(X)] ≤ B min(ε, (2/|e-E|)^q L^q + exp(-|e-E|²/(32σ²)))`, `B = scalarKernelPrefactor scale σ`,
with integrability. All integrability is derived from measurability, `0 ≤ A ≤ 1`, the scalar
kernel bound and the terminal `L^q` bound.
-/
theorem correlated_expectation_localization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A X : Ω → ℝ) (hA : Measurable A) (hX : Measurable X)
    (hA0 : ∀ x, 0 ≤ A x) (hA1 : ∀ x, A x ≤ 1)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M e q L ε : ℝ) (hs : 0 < scale) (hσ : 0 < σ) (hq : 0 < q)
    (hL : 0 ≤ L) (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) (hg : 0 < |e - E|)
    (hwidth : 4 * (M / scale) ≤ |e - E|)
    (hLp : eLpNorm (fun x => X x - e) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal L)
    (hε : (∫ x, A x ∂μ) ≤ ε) :
    Integrable (fun x => A x * scalarConvolution w scale E σ (X x)) μ ∧
      (∫ x, A x * scalarConvolution w scale E σ (X x) ∂μ) ≤
        scalarKernelPrefactor scale σ *
          min ε ((2 / |e - E|) ^ q * L ^ q +
            Real.exp (-|e - E| ^ 2 / (32 * σ ^ 2))) := by
  let B := scalarKernelPrefactor scale σ
  let tail := Real.exp (-|e - E| ^ 2 / (32 * σ ^ 2))
  have hB : 0 ≤ B := by unfold B scalarKernelPrefactor; positivity
  have hkernel := fun x => scalarConvolution_uniform w hw hcompact hunit hw0
    scale E σ M (X x) hs hσ hsupp
  have hprod0 : ∀ x, 0 ≤ A x * scalarConvolution w scale E σ (X x) :=
    fun x => mul_nonneg (hA0 x) (hkernel x).1
  have hprod : ∀ x, A x * scalarConvolution w scale E σ (X x) ≤ B := fun x =>
    (mul_le_of_le_one_left (hkernel x).1 (hA1 x)).trans (hkernel x).2
  have hm : Measurable (fun x => A x * scalarConvolution w scale E σ (X x)) :=
    hA.mul ((measurable_scalarConvolution w hw.measurable scale E σ).comp hX)
  have hi : Integrable (fun x => A x * scalarConvolution w scale E σ (X x)) μ :=
    (integrable_const B).mono' hm.aestronglyMeasurable (ae_of_all μ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hprod0 x)] using hprod x)
  have hAi : Integrable A μ := (integrable_const (1 : ℝ)).mono' hA.aestronglyMeasurable
    (ae_of_all μ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hA0 x)] using hA1 x)
  have hcap : (∫ x, A x * scalarConvolution w scale E σ (X x) ∂μ) ≤ B * ε := by
    calc
      _ ≤ ∫ x, B * A x ∂μ := integral_mono hi (hAi.const_mul B) fun x => by
        simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hkernel x).2 (hA0 x)
      _ = B * ∫ x, A x ∂μ := integral_const_mul _ _
      _ ≤ B * ε := mul_le_mul_of_nonneg_left hε hB
  have hmom := terminal_moment_of_Lq μ X hX e q L hq hL hLp
  have hmajor := ((hmom.1.const_mul ((2 / |e - E|) ^ q)).add (integrable_const tail)).const_mul B
  have hloc : (∫ x, A x * scalarConvolution w scale E σ (X x) ∂μ) ≤
      B * ((2 / |e - E|) ^ q * L ^ q + tail) := by
    calc
      _ ≤ ∫ x, B * ((2 / |e - E|) ^ q * |X x - e| ^ q + tail) ∂μ :=
        integral_mono hi hmajor fun x =>
          (mul_le_of_le_one_left (hkernel x).1 (hA1 x)).trans
            (scalarConvolution_pointwise_localization w hw hcompact hunit hw0
              scale E σ M e (X x) q hs hσ hq hsupp hg hwidth)
      _ = B * ((2 / |e - E|) ^ q * (∫ x, |X x - e| ^ q ∂μ) + tail) := by
        rw [integral_const_mul, integral_add (hmom.1.const_mul _) (integrable_const tail),
          integral_const_mul, integral_const]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left
        (mul_le_mul_of_nonneg_left hmom.2
          (Real.rpow_nonneg
            (show 0 ≤ (2 : ℝ) / |e - E| from
              div_nonneg (by norm_num) (abs_nonneg (e - E))) q)) tail) hB
  refine ⟨hi, ?_⟩
  by_cases hc : ε ≤ (2 / |e - E|) ^ q * L ^ q + tail
  · rw [min_eq_left hc]
    exact hcap
  · rw [min_eq_right (le_of_not_ge hc)]
    exact hloc

end BlockBand.Window.Transfer
