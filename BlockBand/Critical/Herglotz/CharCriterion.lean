module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A characteristic-function bound for small values (`C = 0` step)

* `measureReal_two_div_le_abs_le` — for a real random variable `X` on a probability space,
  `T > 0` and `ε`: if `|1 - E e^{itX}| ≤ ε` for all `t ∈ [0, T]`, then
  `P(|X| ≥ 2/T) ≤ 2ε`.
* `ae_eq_zero_of_integral_cexp_eq_one` — if `E e^{itX} = 1` for every `t ≥ 0`, then `X = 0`
  almost surely (the conclusion `v^*Cv = 0` a.s. of the paper).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology

namespace BlockBand.Critical.Herglotz

/-- `∫_0^T (1 - cos(tx)) dt ≥ T/2` when `|x| ≥ 2/T`. -/
theorem half_le_integral_one_sub_cos {T x : ℝ} (hT : 0 < T) (hx : 2 / T ≤ |x|) :
    T / 2 ≤ ∫ t in (0 : ℝ)..T, (1 - Real.cos (t * x)) := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; have : 0 < 2 / T := by positivity
    linarith
  have hcos : (∫ t in (0 : ℝ)..T, Real.cos (t * x)) = Real.sin (T * x) / x := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T) Real.cos hx0
    simp only [mul_zero] at h
    rw [show (fun t => Real.cos (t * x)) = fun t => Real.cos (x * t) by
      funext t; rw [mul_comm]]
    rw [h, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul, mul_comm x T]
    field_simp
  have hci : IntervalIntegrable (fun t : ℝ => Real.cos (t * x)) volume 0 T :=
    (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hci, hcos,
    intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hb : |Real.sin (T * x) / x| ≤ T / 2 := by
    rw [abs_div]
    have hax : 0 < |x| := abs_pos.mpr hx0
    rw [div_le_iff₀ hax]
    have h1 := Real.abs_sin_le_one (T * x)
    have h2 : 1 ≤ T / 2 * |x| := by
      rw [div_le_iff₀ hT] at hx
      linarith
    linarith
  have := neg_abs_le (Real.sin (T * x) / x)
  have := le_abs_self (Real.sin (T * x) / x)
  linarith

theorem integral_one_sub_cos_nonneg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    0 ≤ ∫ t in (0 : ℝ)..T, (1 - Real.cos (t * x)) :=
  intervalIntegral.integral_nonneg hT fun t _ => by
    have := Real.cos_le_one (t * x); linarith

/-- **Characteristic-function bound for small values.** Law: a real random variable `X`
(measurable) on a probability space `(Ω, P)`. Hypothesis: `|1 - E e^{itX}| ≤ ε` for every
`t ∈ [0, T]`, `T > 0`. Conclusion: `P(|X| ≥ 2/T) ≤ 2ε`. -/
theorem measureReal_two_div_le_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {T ε : ℝ} (hT : 0 < T)
    (hε : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖1 - ∫ ω, cexp (I * t * X ω) ∂P‖ ≤ ε) :
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
    have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) T, (∫ ω, g ω t ∂P) ≤ ε := by
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
      exact (Complex.re_le_norm _).trans (hε t ⟨ht.1.le, ht.2⟩)
    calc (∫ t, ∫ ω, g ω t ∂P ∂ν) ≤ ∫ t, ε ∂ν := by
          refine integral_mono_ae ?_ (integrable_const ε) ?_
          · exact hgint.integral_prod_right
          · simp only [ν]
            exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
      _ = T * ε := by
          simp [ν, integral_const, measureReal_def, hT.le]
  have hT2 : 0 < T / 2 := by positivity
  have : P.real {ω | T / 2 ≤ h (X ω)} ≤ 2 * ε := by
    have h3 : T / 2 * P.real {ω | T / 2 ≤ h (X ω)} ≤ T / 2 * (2 * ε) := by
      linarith
    exact le_of_mul_le_mul_left h3 hT2
  linarith

/-- **`v^*Cv = 0` almost surely**: a real random variable whose characteristic
function equals `1` on `t ≥ 0` vanishes almost surely. -/
theorem ae_eq_zero_of_integral_cexp_eq_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (h : ∀ t : ℝ, 0 ≤ t → (∫ ω, cexp (I * t * X ω) ∂P) = 1) : X =ᵐ[P] 0 := by
  have hn : ∀ n : ℕ, P {ω | 2 / ((n : ℝ) + 1) ≤ |X ω|} = 0 := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb := measureReal_two_div_le_abs_le (P := P) hX hT (ε := 0) fun t ht => by
      rw [h t ht.1, sub_self, norm_zero]
    rw [mul_zero] at hb
    have h0 : P.real {ω | 2 / ((n : ℝ) + 1) ≤ |X ω|} = 0 :=
      le_antisymm hb measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0
  have hsub : {ω | X ω ≠ 0} ⊆ ⋃ n : ℕ, {ω | 2 / ((n : ℝ) + 1) ≤ |X ω|} := by
    intro ω hω
    have hpos : 0 < |X ω| := abs_pos.mpr hω
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / |X ω|)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at hn
    nlinarith
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null hn)

end BlockBand.Critical.Herglotz
