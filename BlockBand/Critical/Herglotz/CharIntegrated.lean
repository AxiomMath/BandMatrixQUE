module

public import BlockBand.Critical.Herglotz.CharCriterion
public import BlockBand.Critical.Herglotz.Kernel

/-!
# Integrated characteristic-function criterion and exponential comparison

* `measureReal_two_div_le_abs_le_of_integral`: integrated form of the characteristic-function tail
  bound. If
  `‖1 - E e^{itX}‖ ≤ b(t)` on `(0, T]` with `∫_{(0,T]} b ≤ T ε`, then `P(|X| ≥ 2/T) ≤ 2ε`
  (no uniformity in `t` is needed; used with pointwise-in-`t` limits and dominated convergence).
* `norm_integral_cexp_sub_le`: for a.e.-measurable `A, B` with `Im A, Im B ≥ 0`, `t, δ ≥ 0`,
  `‖E e^{itA} - E e^{itB}‖ ≤ t δ + 2 P*(‖A - B‖ ≥ δ)` (outer measure).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology ENNReal

namespace BlockBand.Critical.Herglotz

/-- **Integrated characteristic-function bound.** Law: a measurable real `X` on `(Ω, P)`.
Hypotheses: `T > 0`, `b` integrable on `(0, T]` with `∫_{(0,T]} b ≤ Tε`, and
`‖1 - E e^{itX}‖ ≤ b(t)` for `t ∈ (0, T]`. Conclusion: `P(|X| ≥ 2/T) ≤ 2ε`. -/
theorem measureReal_two_div_le_abs_le_of_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {T ε : ℝ}
    (hT : 0 < T) {b : ℝ → ℝ} (hb : Integrable b (volume.restrict (Set.Ioc 0 T)))
    (hbε : ∫ t in Set.Ioc 0 T, b t ≤ T * ε)
    (hφ : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖1 - ∫ ω, cexp (I * t * X ω) ∂P‖ ≤ b t) :
    P.real {ω | 2 / T ≤ |X ω|} ≤ 2 * ε := by
  set h : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..T, (1 - Real.cos (t * x)) with hh
  -- joint integrand on `Ω × (0, T]`
  set g : Ω → ℝ → ℝ := fun ω t => 1 - Real.cos (t * X ω) with hg
  have hgm : Measurable (Function.uncurry g) := by
    simp only [hg]
    fun_prop
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have : IsFiniteMeasure ν := by
    simp only [ν]; infer_instance
  have hgint : Integrable (Function.uncurry g) (P.prod ν) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable 2 (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hg, Real.norm_eq_abs]
    have h1 := Real.cos_le_one (p.2 * X p.1)
    have h2 := Real.neg_one_le_cos (p.2 * X p.1)
    rw [abs_le]; constructor <;> linarith
  have hhX : ∀ ω, h (X ω) = ∫ t, g ω t ∂ν := by
    intro ω
    simp only [hh, hg, ν]
    rw [intervalIntegral.integral_of_le hT.le]
  have hhm : Measurable fun ω => h (X ω) := by
    have := (hgm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have heq : (fun ω => h (X ω)) = fun ω => ∫ y, Function.uncurry g (ω, y) ∂ν := by
      funext ω; exact hhX ω
    rw [heq]; exact this
  have hhint : Integrable (fun ω => h (X ω)) P := by
    refine Integrable.of_bound hhm.aestronglyMeasurable (2 * T)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_one_sub_cos_nonneg hT.le _)]
    show (∫ t in (0 : ℝ)..T, (1 - Real.cos (t * X ω))) ≤ 2 * T
    calc (∫ t in (0 : ℝ)..T, (1 - Real.cos (t * X ω))) ≤ ∫ t in (0 : ℝ)..T, (2 : ℝ) := by
          refine intervalIntegral.integral_mono_on hT.le ?_ intervalIntegrable_const ?_
          · exact (continuous_const.sub (Real.continuous_cos.comp
              (continuous_id.mul continuous_const))).intervalIntegrable _ _
          · intro t _
            have := Real.neg_one_le_cos (t * X ω); linarith
      _ = 2 * T := by simp; ring
  -- Markov
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => integral_one_sub_cos_nonneg hT.le (X ω)) hhint (T / 2)
  have hsub : {ω | 2 / T ≤ |X ω|} ⊆ {ω | T / 2 ≤ h (X ω)} := fun ω hω =>
    half_le_integral_one_sub_cos hT hω
  have hmono : P.real {ω | 2 / T ≤ |X ω|} ≤ P.real {ω | T / 2 ≤ h (X ω)} :=
    measureReal_mono hsub
  -- Fubini and the characteristic-function hypothesis
  have hEh : (∫ ω, h (X ω) ∂P) ≤ T * ε := by
    simp_rw [hhX]
    rw [integral_integral_swap hgint]
    have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) T, (∫ ω, g ω t ∂P) ≤ b t := by
      intro t ht
      have hre : (∫ ω, g ω t ∂P) = (1 - ∫ ω, cexp (I * t * X ω) ∂P).re := by
        rw [Complex.sub_re, Complex.one_re]
        have hcm : Measurable fun ω => cexp (I * t * X ω) := by fun_prop
        have hci : Integrable (fun ω => cexp (I * t * X ω)) P := by
          refine Integrable.of_bound hcm.aestronglyMeasurable 1
            (Eventually.of_forall fun ω => ?_)
          rw [show I * (t : ℂ) * (X ω : ℂ) = ((t * X ω : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        have hc : (∫ ω, cexp (I * t * X ω) ∂P).re = ∫ ω, Real.cos (t * X ω) ∂P := by
          rw [← RCLike.re_eq_complex_re, ← integral_re hci]
          congr 1; funext ω
          rw [RCLike.re_eq_complex_re, show I * (t : ℂ) * (X ω : ℂ) = ((t * X ω : ℝ) : ℂ) * I by
            push_cast; ring, Complex.exp_ofReal_mul_I_re]
        have hcos_int : Integrable (fun ω => Real.cos (t * X ω)) P := by
          refine Integrable.of_bound (by fun_prop : Measurable fun ω => Real.cos (t * X ω)).aestronglyMeasurable 1
            (Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
        rw [hc]
        simp only [hg]
        rw [integral_sub (integrable_const _) hcos_int, integral_const, probReal_univ, one_smul]
      rw [hre]
      exact (Complex.re_le_norm _).trans (hφ t ht)
    calc (∫ t, ∫ ω, g ω t ∂P ∂ν) ≤ ∫ t, b t ∂ν := by
          refine integral_mono_ae ?_ hb ?_
          · exact hgint.integral_prod_right
          · simp only [ν]
            exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
      _ ≤ T * ε := hbε
  have hT2 : 0 < T / 2 := by positivity
  have : P.real {ω | T / 2 ≤ h (X ω)} ≤ 2 * ε := by
    have h3 : T / 2 * P.real {ω | T / 2 ≤ h (X ω)} ≤ T / 2 * (2 * ε) := by
      linarith
    exact le_of_mul_le_mul_left h3 hT2
  linarith

theorem norm_cexp_I_mul_sub_le_min {t : ℝ} (ht : 0 ≤ t) {w w' : ℂ} (hw : 0 ≤ w.im)
    (hw' : 0 ≤ w'.im) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖cexp (I * t * w) - cexp (I * t * w')‖ ≤
      t * δ + 2 * ({p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}.indicator 1 (w, w')) := by
  by_cases h : δ ≤ ‖w - w'‖
  · rw [Set.indicator_of_mem (show (w, w') ∈ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} from h),
      Pi.one_apply, mul_one]
    have h1 := norm_cexp_I_mul_le_one ht hw
    have h2 := norm_cexp_I_mul_le_one ht hw'
    have := norm_sub_le (cexp (I * t * w)) (cexp (I * t * w'))
    nlinarith [mul_nonneg ht hδ]
  · rw [Set.indicator_of_notMem (show (w, w') ∉ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} from h),
      mul_zero, add_zero]
    refine (norm_cexp_I_mul_sub_le ht hw hw').trans ?_
    exact mul_le_mul_of_nonneg_left (not_le.1 h).le ht

/-- **Comparison of bounded analytic exponentials in mean.** Law: a.e.-measurable complex
`A, B` on a probability space `(Ω, P)` with `Im A, Im B ≥ 0` pointwise. For `t, δ ≥ 0`:
`‖E e^{itA} - E e^{itB}‖ ≤ t δ + 2 P*(‖A - B‖ ≥ δ)`. -/
theorem norm_integral_cexp_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Ω → ℂ} (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hAi : ∀ ω, 0 ≤ (A ω).im) (hBi : ∀ ω, 0 ≤ (B ω).im) {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    ‖(∫ ω, cexp (I * t * A ω) ∂P) - ∫ ω, cexp (I * t * B ω) ∂P‖ ≤
      t * δ + 2 * (P {ω | δ ≤ ‖A ω - B ω‖}).toReal := by
  have hint : ∀ W : Ω → ℂ, AEMeasurable W P → (∀ ω, 0 ≤ (W ω).im) →
      Integrable (fun ω => cexp (I * t * W ω)) P := by
    intro W hW hWi
    refine Integrable.of_bound ((Complex.continuous_exp.comp (continuous_const.mul
      continuous_id)).measurable.comp_aemeasurable hW).aestronglyMeasurable 1
      (ae_of_all _ fun ω => norm_cexp_I_mul_le_one ht (hWi ω))
  rw [← integral_sub (hint A hA hAi) (hint B hB hBi)]
  refine (norm_integral_le_integral_norm _).trans ?_
  set S := {ω | δ ≤ ‖A ω - B ω‖} with hS
  have hnn : 0 ≤ᵐ[P] fun ω => ‖cexp (I * t * A ω) - cexp (I * t * B ω)‖ :=
    ae_of_all _ fun _ => norm_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hnn ((hint A hA hAi).sub
    (hint B hB hBi)).norm.aestronglyMeasurable]
  have hpt : ∀ ω, ENNReal.ofReal ‖cexp (I * t * A ω) - cexp (I * t * B ω)‖ ≤
      ENNReal.ofReal (t * δ) + ENNReal.ofReal 2 * S.indicator 1 ω := by
    intro ω
    have h := norm_cexp_I_mul_sub_le_min ht (hAi ω) (hBi ω) hδ
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one, ← ENNReal.ofReal_add
        (mul_nonneg ht hδ) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal (h.trans ?_)
      have : ({p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}.indicator (1 : ℂ × ℂ → ℝ) (A ω, B ω)) ≤ 1 := by
        by_cases hp : (A ω, B ω) ∈ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}
        · rw [Set.indicator_of_mem hp]; simp
        · rw [Set.indicator_of_notMem hp]; norm_num
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
      rw [Set.indicator_of_notMem (show (A ω, B ω) ∉ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} from hω),
        mul_zero, add_zero]
  have hlint : ∫⁻ ω, ENNReal.ofReal ‖cexp (I * t * A ω) - cexp (I * t * B ω)‖ ∂P ≤
      ENNReal.ofReal (t * δ + 2 * (P S).toReal) := by
    calc ∫⁻ ω, ENNReal.ofReal ‖cexp (I * t * A ω) - cexp (I * t * B ω)‖ ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (t * δ) + ENNReal.ofReal 2 * S.indicator 1 ω) ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (t * δ) + ENNReal.ofReal 2 * ∫⁻ ω, S.indicator 1 ω ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (t * δ) + ENNReal.ofReal 2 * P S := by
          gcongr
          exact lintegral_indicator_one_le S
      _ = ENNReal.ofReal (t * δ + 2 * (P S).toReal) := by
          rw [ENNReal.ofReal_add (mul_nonneg ht hδ) (by positivity),
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
            ENNReal.ofReal_toReal (measure_ne_top P S)]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (mul_nonneg ht hδ) (by positivity)) hlint

end BlockBand.Critical.Herglotz
