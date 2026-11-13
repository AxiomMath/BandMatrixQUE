module

public import BlockBand.Internal.Contracts.TransmissionUniform
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# The interior `p = 1` law and every critical limit

* **`InteriorDualLawOne`**: the `p = 1` interior part of `TransmissionLawContract.law` — for
  fixed `b`, bulk `E` and profile `κ`, *some* critical limit `(P, μ)` with, at every `t > 0` and
  interior `(x, y)` (`IsRatioParameter ![x] ![y]`), existence of the dual and the dual identity
  `E F_{x,y}(μ_t) = dualTransform` for every realization. **`interiorDualLawOne_of`**:
  `TransmissionLawContract → InteriorDualLawOne`.
* `ratioIntegrand_one`, `ratioIntegrand_bounds` (`−(x + y/(1−y)) ≤ r ≤ 0` on `[0,1]`),
  `continuousAt_ratioIntegrand` (continuity on `[0,1]` for `x ≥ 0`, `0 ≤ y < 1`, including
  `t = 0`, by the derivative of `log(1−yt) − log(1+xt)`), **`continuous_transmissionRatio`**
  (`ν ↦ F_{x,y}(ν)` is weakly continuous), `transmissionRatio_mem` (`F ∈ (0,1]`).
* **`integral_ratio_eq_of_limits`**: any two critical limits give the same `E F_{x,y}(μ_t)`
  (`fdd` with `k = 1`); **`dualLawValue_of_limit`**: under `InteriorDualLawOne`, every critical
  limit has the interior dual identity at `p = 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **The interior `p = 1` part of the `TransmissionLawContract.law`.** -/
def InteriorDualLawOne : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ x y : ℝ, IsRatioParameter ![x] ![y] →
          HasDualDeletionProcess (transportD0 b E) ![x] ![y] ∧
          DualLawValue E κ t (transportD0 b E) ![x] ![y]
            (∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P)

/-- **The `TransmissionLawContract` gives `InteriorDualLawOne`.** -/
theorem interiorDualLawOne_of (h : TransmissionLawContract) : InteriorDualLawOne := by
  intro b hb hb2 E hE1 hE2 κ hκ
  obtain ⟨Ω, m, P, μ, hlim, hlaw⟩ := h.law b hb hb2 E hE1 hE2 κ hκ
  exact ⟨Ω, m, P, μ, hlim, fun t ht x y hxy => hlaw t ht 1 ![x] ![y] hxy⟩

theorem ratioIntegrand_one (x y t : ℝ) :
    ratioIntegrand ![x] ![y] t =
      if t = 0 then -(x + y) else (Real.log (1 - y * t) - Real.log (1 + x * t)) / t := by
  simp [ratioIntegrand]

/-- `−(x + y/(1−y)) ≤ r_{x,y}(t) ≤ 0` on `[0,1]`. -/
theorem ratioIntegrand_bounds {x y t : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -(x + y / (1 - y)) ≤ ratioIntegrand ![x] ![y] t ∧ ratioIntegrand ![x] ![y] t ≤ 0 := by
  rw [ratioIntegrand_one]
  have hy' : 0 < 1 - y := by linarith
  split_ifs with h
  · have : y ≤ y / (1 - y) := by rw [le_div_iff₀ hy']; nlinarith
    constructor <;> linarith
  · have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    have hyt : y * t ≤ y := mul_le_of_le_one_right hy0 ht1
    have h1 : 0 < 1 - y * t := by linarith
    have h2 : 0 < 1 + x * t := by positivity
    have l1 : Real.log (1 + x * t) ≤ x * t := by linarith [Real.log_le_sub_one_of_pos h2]
    have l2 : 0 ≤ Real.log (1 + x * t) := Real.log_nonneg (by nlinarith)
    have l3 : Real.log (1 - y * t) ≤ 0 := Real.log_nonpos h1.le (by nlinarith)
    have l4 : -(y * t / (1 - y)) ≤ Real.log (1 - y * t) := by
      have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
      rw [Real.log_inv] at h3
      have e : (1 - y * t)⁻¹ - 1 = y * t / (1 - y * t) := by field_simp; ring
      have h4 : y * t / (1 - y * t) ≤ y * t / (1 - y) :=
        div_le_div_of_nonneg_left (by positivity) hy' (by linarith)
      linarith
    have e2 : -(x + y / (1 - y)) * t = -(x * t) - y * t / (1 - y) := by ring
    constructor
    · rw [le_div_iff₀ ht, e2]; linarith
    · rw [div_le_iff₀ ht]; linarith

/-- **`r_{x,y}` is continuous at every `t ∈ [0,1]`.** -/
theorem continuousAt_ratioIntegrand {x y t₀ : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) : ContinuousAt (ratioIntegrand ![x] ![y]) t₀ := by
  have hf : ratioIntegrand ![x] ![y] =
      fun t => if t = 0 then -(x + y) else (Real.log (1 - y * t) - Real.log (1 + x * t)) / t :=
    funext (ratioIntegrand_one x y)
  rw [hf]
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h
    have h1 : HasDerivAt (fun t => 1 - y * t) (-y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul y).const_sub 1
    have h2 : HasDerivAt (fun t => 1 + x * t) x 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul x).const_add 1
    have hd := (h1.log (by simp)).sub (h2.log (by simp))
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have e : -y / (1 - y * 0) - x / (1 + x * 0) = -(x + y) := by ring
    rw [e] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp [ht', div_eq_inv_mul]
  · have hpos1 : 0 < 1 - y * t₀ := by nlinarith
    have hpos2 : 0 < 1 + x * t₀ := by positivity
    have hc : ContinuousAt (fun t => (Real.log (1 - y * t) - Real.log (1 + x * t)) / t) t₀ :=
      (((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).log hpos1.ne').sub
        ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).log hpos2.ne')).div
        continuousAt_id h.ne'
    refine hc.congr ?_
    filter_upwards [eventually_ne_nhds h.ne'] with t ht
    simp [ht]

/-- `r_{x,y}` as a bounded continuous function on `[0,1]`. -/
def ratioBCF {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) : unitInterval →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun t => ratioIntegrand ![x] ![y] (t : ℝ),
    continuous_iff_continuousAt.2 fun t =>
      (continuousAt_ratioIntegrand hx hy0 hy1 t.2.1 t.2.2).comp continuous_subtype_val.continuousAt⟩

/-- **`ν ↦ F_{x,y}(ν)` is weakly continuous** (`x ≥ 0`, `0 ≤ y < 1`). -/
theorem continuous_transmissionRatio {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Continuous fun ν : FiniteMeasure unitInterval => transmissionRatio ![x] ![y] ν := by
  refine Real.continuous_exp.comp (continuous_iff_continuousAt.2 fun ν => ?_)
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 (tendsto_id (x := 𝓝 ν))
    (ratioBCF hx hy0 hy1)

theorem transmissionRatio_mem {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (ν : FiniteMeasure unitInterval) :
    0 < transmissionRatio ![x] ![y] ν ∧ transmissionRatio ![x] ![y] ν ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (integral_nonpos fun t => ?_)⟩
  exact (ratioIntegrand_bounds hx hy0 hy1 t.2.1 t.2.2).2

/-- `F_{x,y}` of the single coordinate, as a test of `fdd` with `k = 1`. -/
def ratioTest {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => transmissionRatio ![x] ![y] (ν 0),
      (continuous_transmissionRatio hx hy0 hy1).comp (continuous_apply 0)⟩ 1 fun a b => by
    have ha := transmissionRatio_mem hx hy0 hy1 (a 0)
    have hb := transmissionRatio_mem hx hy0 hy1 (b 0)
    simp only [ContinuousMap.coe_mk]
    rw [Real.dist_eq, abs_le]; constructor <;> linarith

/-- **Two critical limits give the same `E F_{x,y}(μ_t)`.** -/
theorem integral_ratio_eq_of_limits {b E : ℝ} {κ : ℝ → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {μ' : ℝ → Ω' → FiniteMeasure unitInterval}
    (hP : IsTransmissionLimit b E κ P μ) (hP' : IsTransmissionLimit b E κ P' μ') {t : ℝ}
    (ht : 0 < t) {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P =
      ∫ ω, transmissionRatio ![x] ![y] (μ' t ω) ∂P' := by
  have h1 := hP.fdd 1 (fun _ => t) (fun _ => ht) (ratioTest hx hy0 hy1)
  have h2 := hP'.fdd 1 (fun _ => t) (fun _ => ht) (ratioTest hx hy0 hy1)
  exact tendsto_nhds_unique h1 h2

/-- **Under `InteriorDualLawOne`, every critical limit has the interior dual identity.** -/
theorem dualLawValue_of_limit (hInt : InteriorDualLawOne) {b : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hP : IsTransmissionLimit b E κ P μ) {t : ℝ} (ht : 0 < t) {x y : ℝ}
    (hxy : IsRatioParameter ![x] ![y]) :
    DualLawValue E κ t (transportD0 b E) ![x] ![y]
      (∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P) := by
  obtain ⟨Ω', m', P', μ', hP', hlaw⟩ := hInt b hb hb2 E hE1 hE2 κ hκ
  have hx : 0 ≤ x := by simpa using (hxy.2.2.1 0).le
  have hy := hxy.2.2.2 0
  simp only [Matrix.cons_val_fin_one] at hy
  rw [integral_ratio_eq_of_limits hP hP' ht hx hy.1.le hy.2]
  exact (hlaw t ht x y hxy).2

end BlockBand.Transmission.DualBoundary
