module

public import BlockBand.Transmission.DualBoundary.LawInterior

/-!
# Continuity of `V(t) = E F_{x,y}(μ_t)` in `t` and in `(x, y)`

Setting: a critical limit `IsTransmissionLimit b E κ P μ`; parameters `x ≥ 0`, `0 ≤ y < 1`.
* `measurable_transmissionRatio`: `ν ↦ F_{x,y}(ν)` is measurable for the Giry σ-algebra of
  `FiniteMeasure [0,1]` (the one in which `μ_t` is measurable).
* **`continuousAt_integral_ratio`**: `t ↦ E F_{x,y}(μ_t)` is continuous at every `t₀ > 0`
  (the `continuous` field, dominated convergence).
* `tendsto_ratioIntegrand`, `tendsto_transmissionRatio_param`: `F_{x_n,y_n}(ν) → F_{x,y}(ν)`
  along parameters `x_n → x`, `y_n → y` with `0 ≤ x_n ≤ X`, `0 ≤ y_n ≤ y_max < 1`;
  **`tendsto_integral_ratio_param`**: the same for `E F(μ_t)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped NNReal ENNReal BoundedContinuousFunction

theorem measurable_transmissionRatio {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Measurable fun ν : FiniteMeasure unitInterval => transmissionRatio ![x] ![y] ν := by
  have hr : Measurable fun t : unitInterval => ratioIntegrand ![x] ![y] (t : ℝ) :=
    (ratioBCF hx hy0 hy1).continuous.measurable
  have e : (fun ν : FiniteMeasure unitInterval => transmissionRatio ![x] ![y] ν) = fun ν : FiniteMeasure unitInterval =>
      Real.exp (-(∫⁻ t, ENNReal.ofReal (-ratioIntegrand ![x] ![y] (t : ℝ))
        ∂(ν : Measure unitInterval)).toReal) := by
    funext ν
    rw [transmissionRatio, ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t =>
      neg_nonneg.2 (ratioIntegrand_bounds hx hy0 hy1 t.2.1 t.2.2).2) hr.neg.aestronglyMeasurable,
      integral_neg, neg_neg]
  rw [e]
  exact Real.continuous_exp.measurable.comp (ENNReal.measurable_toReal.comp
    ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hr.neg)).comp
      measurable_subtype_coe)).neg

variable {b E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {μ : ℝ → Ω → FiniteMeasure unitInterval}

/-- **`t ↦ E F_{x,y}(μ_t)` is continuous on `(0, ∞)`.** -/
theorem continuousAt_integral_ratio (hP : IsTransmissionLimit b E κ P μ) {t₀ : ℝ}
    (ht₀ : 0 < t₀) {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ContinuousAt (fun t => ∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P) t₀ := by
  have := hP.prob
  refine continuousAt_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · filter_upwards [Ioi_mem_nhds ht₀] with t ht
    exact ((measurable_transmissionRatio hx hy0 hy1).comp
      (hP.measurable t ht)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => Eventually.of_forall fun ω => ?_
    have := transmissionRatio_mem hx hy0 hy1 (μ t ω)
    rw [Real.norm_eq_abs, abs_of_pos this.1]; exact this.2
  · filter_upwards [hP.continuous] with ω hω
    exact (continuous_transmissionRatio hx hy0 hy1).continuousAt.comp
      (hω.continuousAt (Ioi_mem_nhds ht₀))

theorem tendsto_ratioIntegrand {xs ys : ℕ → ℝ} {x y : ℝ} (hxs : Tendsto xs atTop (𝓝 x))
    (hys : Tendsto ys atTop (𝓝 y)) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun n => ratioIntegrand ![xs n] ![ys n] t) atTop
      (𝓝 (ratioIntegrand ![x] ![y] t)) := by
  simp only [ratioIntegrand_one]
  split_ifs with h
  · exact (hxs.add hys).neg
  · have h1 : 0 < 1 - y * t := by nlinarith
    have h2 : 0 < 1 + x * t := by positivity
    exact (((tendsto_const_nhds.sub (hys.mul_const t)).log h1.ne').sub
      ((tendsto_const_nhds.add (hxs.mul_const t)).log h2.ne')).div_const t

/-- **`F_{x_n,y_n}(ν) → F_{x,y}(ν)`.** -/
theorem tendsto_transmissionRatio_param {xs ys : ℕ → ℝ} {x y : ℝ}
    (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y)) (hx : 0 ≤ x) (hy0 : 0 ≤ y)
    (hy1 : y < 1) (hxs0 : ∀ n, 0 ≤ xs n) (hys0 : ∀ n, 0 ≤ ys n) {ymax X : ℝ}
    (hymax : ∀ n, ys n ≤ ymax) (hymax1 : ymax < 1) (hX : ∀ n, xs n ≤ X)
    (ν : FiniteMeasure unitInterval) :
    Tendsto (fun n => transmissionRatio ![xs n] ![ys n] ν) atTop
      (𝓝 (transmissionRatio ![x] ![y] ν)) := by
  refine (Real.continuous_exp.tendsto _).comp ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => X + ymax / (1 - ymax))
    (fun n => ?_) (integrable_const _) (fun n => Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun t => tendsto_ratioIntegrand hxs hys hx hy0 hy1 t.2.1 t.2.2)
  · exact (ratioBCF (hxs0 n) (hys0 n) ((hymax n).trans_lt hymax1)).continuous.measurable
      |>.aestronglyMeasurable
  · have hb := ratioIntegrand_bounds (hxs0 n) (hys0 n) ((hymax n).trans_lt hymax1) t.2.1 t.2.2
    have hq : ys n / (1 - ys n) ≤ ymax / (1 - ymax) :=
      div_le_div₀ (by linarith [hys0 n, hymax n]) (hymax n) (by linarith) (by linarith [hymax n])
    have hq0 : 0 ≤ ys n / (1 - ys n) :=
      div_nonneg (hys0 n) (by linarith [hymax n])
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hX n, hxs0 n]

/-- **`E F_{x_n,y_n}(μ_t) → E F_{x,y}(μ_t)`.** -/
theorem tendsto_integral_ratio_param (hP : IsTransmissionLimit b E κ P μ) {t : ℝ} (ht : 0 < t)
    {xs ys : ℕ → ℝ} {x y : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y))
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hxs0 : ∀ n, 0 ≤ xs n) (hys0 : ∀ n, 0 ≤ ys n)
    {ymax X : ℝ} (hymax : ∀ n, ys n ≤ ymax) (hymax1 : ymax < 1) (hX : ∀ n, xs n ≤ X) :
    Tendsto (fun n => ∫ ω, transmissionRatio ![xs n] ![ys n] (μ t ω) ∂P) atTop
      (𝓝 (∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P)) := by
  have := hP.prob
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
    (integrable_const 1) (fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => tendsto_transmissionRatio_param hxs hys hx hy0 hy1 hxs0 hys0
      hymax hymax1 hX (μ t ω))
  · exact ((measurable_transmissionRatio (hxs0 n) (hys0 n) ((hymax n).trans_lt hymax1)).comp
      (hP.measurable t ht)).aestronglyMeasurable
  · have := transmissionRatio_mem (hxs0 n) (hys0 n) ((hymax n).trans_lt hymax1) (μ t ω)
    rw [Real.norm_eq_abs, abs_of_pos this.1]; exact this.2

end BlockBand.Transmission.DualBoundary
