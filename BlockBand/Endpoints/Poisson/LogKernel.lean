module

public import BlockBand.Endpoints.Poisson.FiniteLogDefs

/-!
# Kernel facts for the finite-log recovery

Properties of the Cauchy kernel `p_t` and of the logarithmic kernel `k_δ`, its average over
`t ∈ [0, δ]`:

- `integral_poissonKernel`: `∫ p_t = 1` for `t > 0` (`integrable_poissonKernel`);
- `logKernel_eq_average`: `k_δ(x) = δ⁻¹ ∫_0^δ p_t(x) dt` for `x ≠ 0`;
- `logKernel_nonneg`, `integrable_logKernel`, `integral_logKernel` (`∫ k_δ = 1`), by Tonelli;
- `lintegral_logKernel_mul_min_le`: for `δ > 0`, `a, b ≥ 0`,
  `∫ k_δ(s) min (a|s|, b) ds ≤ 2 (a + b) δ (1 + |log δ|)` (the moment estimate).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Real
open scoped ENNReal

/-- `p_t(x) = (π t)⁻¹ (1 + (x/t)²)⁻¹` for `t > 0`. -/
theorem poissonKernel_eq_mul {t : ℝ} (ht : 0 < t) (x : ℝ) :
    poissonKernel t x = (π * t)⁻¹ * (1 + (x / t) ^ 2)⁻¹ := by
  unfold poissonKernel
  have := Real.pi_pos
  field_simp
  ring

/-- The Cauchy kernel `p_t` is integrable for `t > 0`. -/
theorem integrable_poissonKernel {t : ℝ} (ht : 0 < t) : Integrable (poissonKernel t) := by
  have h := (integrable_inv_one_add_sq.comp_div ht.ne').const_mul (π * t)⁻¹
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [poissonKernel_eq_mul ht x]

/-- The Cauchy kernel has mass one: `∫ p_t = 1` for `t > 0`. -/
theorem integral_poissonKernel {t : ℝ} (ht : 0 < t) : ∫ x, poissonKernel t x = 1 := by
  simp_rw [poissonKernel_eq_mul ht]
  rw [integral_const_mul, Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹) t,
    integral_univ_inv_one_add_sq, abs_of_pos ht, smul_eq_mul]
  have := Real.pi_pos
  field_simp

/-- For `x ≠ 0`, `t ↦ (2π)⁻¹ log (x² + t²)` is a primitive of `t ↦ p_t(x)`. -/
theorem hasDerivAt_poissonKernel_primitive {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (2 * π)⁻¹ * Real.log (x ^ 2 + t ^ 2)) (poissonKernel t x) t := by
  have hpos : 0 < x ^ 2 + t ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add (x ^ 2)
  have h2 := (h1.log hpos.ne').const_mul (2 * π)⁻¹
  convert h2 using 1
  unfold poissonKernel
  have := Real.pi_pos
  field_simp

/-- For `x ≠ 0`, `t ↦ p_t(x)` is continuous. -/
theorem continuous_poissonKernel_left {x : ℝ} (hx : x ≠ 0) :
    Continuous fun t => poissonKernel t x := by
  unfold poissonKernel
  refine continuous_id.div (continuous_const.mul (by fun_prop)) fun t => ?_
  have : 0 < x ^ 2 + t ^ 2 := by positivity
  positivity

/-- `p_t(x) ≥ 0` for `t ≥ 0`. -/
theorem poissonKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : 0 ≤ poissonKernel t x := by
  unfold poissonKernel
  have := Real.pi_pos
  positivity

/-- `k_δ(x) = δ⁻¹ ∫_0^δ p_t(x) dt` for `x ≠ 0` (every real `δ`). -/
theorem logKernel_eq_average (δ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    logKernel δ x = δ⁻¹ * ∫ t in (0 : ℝ)..δ, poissonKernel t x := by
  have hcont := continuous_poissonKernel_left hx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_poissonKernel_primitive hx t)
    (hcont.intervalIntegrable _ _)]
  unfold logKernel
  have hx2 : 0 < x ^ 2 := by positivity
  have : 1 + δ ^ 2 / x ^ 2 = (x ^ 2 + δ ^ 2) / x ^ 2 := by field_simp
  rw [this, Real.log_div (by positivity) hx2.ne']
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [mul_inv]
  ring

/-- `k_δ ≥ 0` for `δ ≥ 0`. -/
theorem logKernel_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : 0 ≤ logKernel δ x := by
  unfold logKernel
  have := Real.pi_pos
  have : 0 ≤ Real.log (1 + δ ^ 2 / x ^ 2) := Real.log_nonneg (by
    have : 0 ≤ δ ^ 2 / x ^ 2 := by positivity
    linarith)
  positivity

/-- `k_δ` is measurable. -/
theorem measurable_logKernel (δ : ℝ) : Measurable (logKernel δ) := by
  unfold logKernel
  fun_prop

/-- Tonelli form of the unit mass: `∫⁻ k_δ = 1` for `δ > 0`. -/
theorem lintegral_ofReal_logKernel {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x, ENNReal.ofReal (logKernel δ x) = 1 := by
  have hp : ∀ t ∈ Set.Ioc (0 : ℝ) δ, ∫⁻ x, ENNReal.ofReal (poissonKernel t x) = 1 := by
    intro t ht
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel ht.1)
      (Filter.Eventually.of_forall fun x => poissonKernel_nonneg ht.1.le x),
      integral_poissonKernel ht.1, ENNReal.ofReal_one]
  have hk : ∀ x : ℝ, x ≠ 0 → ENNReal.ofReal (logKernel δ x) =
      ENNReal.ofReal δ⁻¹ *
        ∫⁻ t in Set.Ioc (0 : ℝ) δ, ENNReal.ofReal (poissonKernel t x) := by
    intro x hx
    rw [logKernel_eq_average δ hx, intervalIntegral.integral_of_le hδ.le,
      ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), ofReal_integral_eq_lintegral_ofReal
        ((continuous_poissonKernel_left hx).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact poissonKernel_nonneg ht.1.le x
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 :=
    compl_mem_ae_iff.mpr (measure_singleton 0)
  have hmeas : Measurable
      (Function.uncurry fun (x t : ℝ) => ENNReal.ofReal (poissonKernel t x)) := by
    unfold poissonKernel
    fun_prop
  calc ∫⁻ x, ENNReal.ofReal (logKernel δ x)
      = ∫⁻ x, ENNReal.ofReal δ⁻¹ *
          ∫⁻ t in Set.Ioc (0 : ℝ) δ, ENNReal.ofReal (poissonKernel t x) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hne] with x hx
        exact hk x hx
    _ = ENNReal.ofReal δ⁻¹ *
          ∫⁻ x, ∫⁻ t in Set.Ioc (0 : ℝ) δ, ENNReal.ofReal (poissonKernel t x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal δ⁻¹ *
          ∫⁻ t in Set.Ioc (0 : ℝ) δ, ∫⁻ x, ENNReal.ofReal (poissonKernel t x) := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ = ENNReal.ofReal δ⁻¹ * ∫⁻ t in Set.Ioc (0 : ℝ) δ, 1 := by
        rw [setLIntegral_congr_fun measurableSet_Ioc hp]
    _ = 1 := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, one_mul, sub_zero,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_cancel₀ hδ.ne',
          ENNReal.ofReal_one]

/-- `k_δ` is integrable for `δ > 0`. -/
theorem integrable_logKernel {δ : ℝ} (hδ : 0 < δ) : Integrable (logKernel δ) := by
  refine ⟨(measurable_logKernel δ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (logKernel_nonneg hδ.le)),
    lintegral_ofReal_logKernel hδ]
  exact ENNReal.one_lt_top

/-- `k_δ` has mass one: `∫ k_δ = 1` for `δ > 0`. -/
theorem integral_logKernel {δ : ℝ} (hδ : 0 < δ) : ∫ x, logKernel δ x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (logKernel_nonneg hδ.le))
    (measurable_logKernel δ).aestronglyMeasurable, lintegral_ofReal_logKernel hδ,
    ENNReal.toReal_one]

/-- `log (1 + z²) ≤ 2z` for `z ≥ 0`. -/
theorem finiteLog_log_one_add_sq_le {z : ℝ} (hz : 0 ≤ z) : Real.log (1 + z ^ 2) ≤ 2 * z := by
  have h1 : Real.log (1 + z ^ 2) ≤ Real.log ((1 + z) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith)
  push_cast at h1
  linarith

/-- `log (1 + y) ≤ y` for `y ≥ 0`. -/
theorem finiteLog_log_one_add_le {y : ℝ} (hy : 0 ≤ y) : Real.log (1 + y) ≤ y := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith)
  linarith

/-- `|s| log (1 + δ²/s²) ≤ 4δ² / (|s| + δ)` for `δ > 0` (all `s`, Lean's `δ²/0 = 0`). -/
theorem abs_mul_log_one_add_div_sq_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    |s| * Real.log (1 + δ ^ 2 / s ^ 2) ≤ 4 * δ ^ 2 / (|s| + δ) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [abs_zero, zero_mul]
    positivity
  have hr : 0 < |s| := abs_pos.2 hs
  have hs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  rw [hs2]
  have hA : Real.log (1 + δ ^ 2 / |s| ^ 2) ≤ 2 * (δ / |s|) := by
    have := finiteLog_log_one_add_sq_le (show 0 ≤ δ / |s| by positivity)
    rwa [div_pow] at this
  have hB : Real.log (1 + δ ^ 2 / |s| ^ 2) ≤ δ ^ 2 / |s| ^ 2 :=
    finiteLog_log_one_add_le (by positivity)
  have hA' : |s| * Real.log (1 + δ ^ 2 / |s| ^ 2) ≤ 2 * δ := by
    have := mul_le_mul_of_nonneg_left hA hr.le
    calc _ ≤ |s| * (2 * (δ / |s|)) := this
      _ = 2 * δ := by field_simp
  have hB' : |s| * Real.log (1 + δ ^ 2 / |s| ^ 2) ≤ δ ^ 2 / |s| := by
    have := mul_le_mul_of_nonneg_left hB hr.le
    calc _ ≤ |s| * (δ ^ 2 / |s| ^ 2) := this
      _ = δ ^ 2 / |s| := by field_simp
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |s| δ with h | h
  · nlinarith
  · have : δ ^ 2 / |s| * (|s| + δ) ≤ 4 * δ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hr]
      nlinarith
    nlinarith

/-- Pointwise majorant:
`k_δ(s) min (a|s|, b) ≤ 1_{[-1,1]}(s) (2aδ/π)(|s| + δ)⁻¹ + (bδ/π)(1 + s²)⁻¹`. -/
theorem logKernel_mul_min_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℝ) :
    logKernel δ s * min (a * |s|) b ≤
      (Set.Icc (-1 : ℝ) 1).indicator (fun s => 2 * a * δ / π * (|s| + δ)⁻¹) s +
        b * δ / π * (1 + s ^ 2)⁻¹ := by
  have hpi := Real.pi_pos
  have hk := logKernel_nonneg hδ.le s
  have hsd : 0 < |s| + δ := by positivity
  by_cases hs : s ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hs]
    have h1 : logKernel δ s * min (a * |s|) b ≤ logKernel δ s * (a * |s|) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hk
    have h2 : logKernel δ s * (a * |s|) ≤ 2 * a * δ / π * (|s| + δ)⁻¹ := by
      have := abs_mul_log_one_add_div_sq_le hδ s
      unfold logKernel
      calc (2 * π * δ)⁻¹ * Real.log (1 + δ ^ 2 / s ^ 2) * (a * |s|)
          = (2 * π * δ)⁻¹ * a * (|s| * Real.log (1 + δ ^ 2 / s ^ 2)) := by ring
        _ ≤ (2 * π * δ)⁻¹ * a * (4 * δ ^ 2 / (|s| + δ)) := by gcongr
        _ = 2 * a * δ / π * (|s| + δ)⁻¹ := by field_simp; ring
    have h3 : 0 ≤ b * δ / π * (1 + s ^ 2)⁻¹ := by positivity
    linarith
  · rw [Set.indicator_of_notMem hs, zero_add]
    have hs1 : 1 < |s| := by
      by_contra h
      exact hs (abs_le.1 (not_lt.1 h))
    have hs2 : 1 < s ^ 2 := by
      have := sq_abs s
      nlinarith
    have h1 : logKernel δ s * min (a * |s|) b ≤ logKernel δ s * b :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hk
    have hl : Real.log (1 + δ ^ 2 / s ^ 2) ≤ δ ^ 2 / s ^ 2 :=
      finiteLog_log_one_add_le (by positivity)
    have hq : δ ^ 2 / s ^ 2 ≤ 2 * δ ^ 2 * (1 + s ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity), mul_assoc, mul_comm _ (s ^ 2), ← mul_assoc,
        ← div_eq_mul_inv, mul_div_assoc]
      have : s ^ 2 / (1 + s ^ 2) ≥ 1 / 2 := by
        rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      nlinarith [sq_nonneg δ]
    have h2 : logKernel δ s * b ≤ b * δ / π * (1 + s ^ 2)⁻¹ := by
      unfold logKernel
      calc (2 * π * δ)⁻¹ * Real.log (1 + δ ^ 2 / s ^ 2) * b
          ≤ (2 * π * δ)⁻¹ * (2 * δ ^ 2 * (1 + s ^ 2)⁻¹) * b := by
            gcongr
            exact hl.trans hq
        _ = b * δ / π * (1 + s ^ 2)⁻¹ := by field_simp
    linarith

/-- `∫_{-1}^{1} (|s| + δ)⁻¹ ds = 2 log ((1 + δ)/δ)` for `δ > 0`. -/
theorem finiteLog_integral_inv_abs_add {δ : ℝ} (hδ : 0 < δ) :
    ∫ s in (-1 : ℝ)..1, (|s| + δ)⁻¹ = 2 * Real.log ((1 + δ) / δ) := by
  have hc : Continuous fun s : ℝ => (|s| + δ)⁻¹ :=
    (continuous_abs.add continuous_const).inv₀ fun s => (by positivity : (0 : ℝ) < |s| + δ).ne'
  have hpos : ∫ s in (0 : ℝ)..1, (|s| + δ)⁻¹ = Real.log ((1 + δ) / δ) := by
    rw [intervalIntegral.integral_congr (g := fun s => (s + δ)⁻¹) fun s hs => by
      rw [Set.uIcc_of_le zero_le_one] at hs
      simp only [abs_of_nonneg hs.1]]
    rw [intervalIntegral.integral_comp_add_right (fun x => x⁻¹) δ, zero_add,
      integral_inv_of_pos hδ (by linarith)]
  have hneg : ∫ s in (-1 : ℝ)..0, (|s| + δ)⁻¹ = ∫ s in (0 : ℝ)..1, (|s| + δ)⁻¹ := by
    have := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0)
      (fun s : ℝ => (|s| + δ)⁻¹)
    simp only [abs_neg, neg_zero, neg_neg] at this
    exact this
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hneg, hpos]
  ring

/-- `log ((1 + δ)/δ) ≤ 1 + |log δ|` for `δ > 0`. -/
theorem finiteLog_log_one_add_div_le {δ : ℝ} (hδ : 0 < δ) :
    Real.log ((1 + δ) / δ) ≤ 1 + |Real.log δ| := by
  rcases le_or_gt δ 1 with h | h
  · rw [Real.log_div (by linarith) hδ.ne']
    have := finiteLog_log_one_add_le hδ.le
    have := neg_le_abs (Real.log δ)
    linarith
  · have := Real.log_le_sub_one_of_pos (show 0 < (1 + δ) / δ by positivity)
    have : (1 + δ) / δ - 1 ≤ 1 := by
      rw [div_sub_one hδ.ne', div_le_one hδ]
      linarith
    have := abs_nonneg (Real.log δ)
    linarith

/-- Moment estimate: for `δ > 0`, `a, b ≥ 0`,
`∫⁻ k_δ(s) min (a|s|, b) ds ≤ 2 (a + b) δ (1 + |log δ|)`. -/
theorem lintegral_logKernel_mul_min_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ s, ENNReal.ofReal (logKernel δ s * min (a * |s|) b) ≤
      ENNReal.ofReal (2 * (a + b) * (δ * (1 + |Real.log δ|))) := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun s => 2 * a * δ / π * (|s| + δ)⁻¹ with hg
  have hgc : Continuous g :=
    continuous_const.mul ((continuous_abs.add continuous_const).inv₀ fun s =>
      (by positivity : (0 : ℝ) < |s| + δ).ne')
  have hgi : Integrable ((Set.Icc (-1 : ℝ) 1).indicator g) :=
    (hgc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hgn : 0 ≤ (Set.Icc (-1 : ℝ) 1).indicator g := fun s =>
    Set.indicator_nonneg (fun s _ => by simp only [hg]; positivity) s
  have hhi : Integrable fun s : ℝ => b * δ / π * (1 + s ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hI1 : ∫ s, (Set.Icc (-1 : ℝ) 1).indicator g s =
      2 * a * δ / π * (2 * Real.log ((1 + δ) / δ)) := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num), hg, intervalIntegral.integral_const_mul,
      finiteLog_integral_inv_abs_add hδ]
  have hI2 : ∫ s : ℝ, b * δ / π * (1 + s ^ 2)⁻¹ = b * δ := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
    field_simp
  calc ∫⁻ s, ENNReal.ofReal (logKernel δ s * min (a * |s|) b)
      ≤ ∫⁻ s, (ENNReal.ofReal ((Set.Icc (-1 : ℝ) 1).indicator g s) +
          ENNReal.ofReal (b * δ / π * (1 + s ^ 2)⁻¹)) := by
        refine lintegral_mono fun s => ?_
        rw [← ENNReal.ofReal_add (hgn s) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (logKernel_mul_min_le hδ ha hb s)
    _ = ENNReal.ofReal (∫ s, (Set.Icc (-1 : ℝ) 1).indicator g s) +
          ENNReal.ofReal (∫ s : ℝ, b * δ / π * (1 + s ^ 2)⁻¹) := by
        rw [lintegral_add_left (hgc.measurable.indicator measurableSet_Icc).ennreal_ofReal,
          ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hgn),
          ofReal_integral_eq_lintegral_ofReal hhi (Filter.Eventually.of_forall fun s => by
            positivity)]
    _ ≤ ENNReal.ofReal (2 * (a + b) * (δ * (1 + |Real.log δ|))) := by
        rw [hI1, hI2, ← ENNReal.ofReal_add (by
          have := Real.log_nonneg (show (1 : ℝ) ≤ (1 + δ) / δ by
            rw [le_div_iff₀ hδ]; linarith)
          positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hL := finiteLog_log_one_add_div_le hδ
        have hL0 : 0 ≤ Real.log ((1 + δ) / δ) := Real.log_nonneg (by
            rw [le_div_iff₀ hδ]; linarith)
        have hpi2 : 2 ≤ π := by linarith [Real.pi_gt_three]
        have hab : 2 * a * δ / π * (2 * Real.log ((1 + δ) / δ)) ≤
            2 * a * (δ * (1 + |Real.log δ|)) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
          have h0 : 0 ≤ a * δ := by positivity
          have h1 : 0 ≤ a * δ * (1 + |Real.log δ|) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hL h0, mul_le_mul_of_nonneg_left hpi2 h1]
        have : b * δ ≤ 2 * b * (δ * (1 + |Real.log δ|)) := by
          have : 0 ≤ b * δ := by positivity
          nlinarith [abs_nonneg (Real.log δ)]
        linarith

end BlockBand.Endpoints
