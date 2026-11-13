module

public import BlockBand.Transmission.LawDuality.PowerLimit
public import BlockBand.Transmission.LawFinite.Interface

/-!
# The entrance of every subsequential limit

* `ratioIntegrand_one_le`: `r_{x,y}(t) ≤ -(x/(1+x) + y)` on `[0,1]`;
* `transmissionRatio_le_exp_mass`: `F_{x,y}(ν) ≤ exp(-(x₀/(1+x₀) + y₀) ν[0,1])` (one pair `0`);
* `integral_ratio_finite_le`: at finite `W`, `E F(μ_W(s)) ≤ P(min_{r ≤ sW} g_r ≤ K) + e^{-cK}`;
* **`hasRatioEntrance_of`**: from the finite-`W` entrance bound
  `LawFinite.TransmissionEntranceBulk`, every subsequential limit (any admissible `κ`) has
  `HasRatioEntrance`, the second clause of `SubLimitRatioMP`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.DualBoundary BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal BoundedContinuousFunction

theorem ratioIntegrand_one_le {x y t : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ratioIntegrand ![x] ![y] t ≤ -(x / (1 + x) + y) := by
  rw [ratioIntegrand_one]
  split_ifs with h
  · have : x / (1 + x) ≤ x := div_le_self hx (by linarith)
    linarith
  · have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    have h1 : 0 < 1 - y * t := by nlinarith
    have h2 : 0 < 1 + x * t := by positivity
    have l1 : Real.log (1 - y * t) ≤ -(y * t) := by linarith [Real.log_le_sub_one_of_pos h1]
    have l2 : x * t / (1 + x) ≤ Real.log (1 + x * t) := by
      have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 h2)
      rw [Real.log_inv] at h3
      have e : (1 + x * t)⁻¹ - 1 = -(x * t / (1 + x * t)) := by field_simp; ring
      have h4 : x * t / (1 + x) ≤ x * t / (1 + x * t) :=
        div_le_div_of_nonneg_left (by positivity) h2 (by nlinarith)
      linarith
    rw [div_le_iff₀ ht]
    have : -(x / (1 + x) + y) * t = -(y * t) - x * t / (1 + x) := by field_simp; ring
    linarith

theorem transmissionRatio_le_exp_mass {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) (i0 : Fin p)
    (ν : FiniteMeasure unitInterval) :
    transmissionRatio x y ν ≤
      Real.exp (-(x i0 / (1 + x i0) + y i0) * (ν : Measure unitInterval).real univ) := by
  unfold transmissionRatio
  refine Real.exp_le_exp.2 ?_
  have hle : ∀ t : unitInterval, ratioIntegrand x y t ≤ -(x i0 / (1 + x i0) + y i0) := by
    intro t
    rw [ratioIntegrand_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    have h1 := ratioIntegrand_one_le (h.1 i0) (h.2 i0).1 (h.2 i0).2 t.2.1 t.2.2
    have h2 : ∑ j ∈ Finset.univ.erase i0, ratioIntegrand ![x j] ![y j] t ≤ 0 :=
      Finset.sum_nonpos fun j _ =>
        (ratioIntegrand_bounds (h.1 j) (h.2 j).1 (h.2 j).2 t.2.1 t.2.2).2
    linarith
  calc ∫ t, ratioIntegrand x y (t : ℝ) ∂(ν : Measure unitInterval)
      ≤ ∫ _t, -(x i0 / (1 + x i0) + y i0) ∂(ν : Measure unitInterval) :=
        integral_mono (integrable_ratioIntegrand h ν) (integrable_const _) hle
    _ = _ := by rw [integral_const, smul_eq_mul]; ring

variable {b E : ℝ} {κ : ℝ → ℝ} {W : ℕ}

theorem mass_transmissionProcess (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ s : ℝ,
      (transmissionProcess b E κ W s ω : Measure unitInterval).real univ =
        conductanceOf (pathTransmission b E κ W ⌊(W : ℝ) * s⌋₊ ω) := by
  filter_upwards [ae_integral_pow_transmissionProcess (W := W) hκ hb hE1 hE2] with ω hω
  intro s
  have := hω 0 s
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, zero_add, pow_one] at this
  exact this

/-- **Finite-`W` entrance bound**: `E F_z(μ_W(s)) ≤ P(min_{1 ≤ r ≤ sW} g_r ≤ K) + e^{-cK}`. -/
theorem integral_ratio_finite_le (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) (i0 : Fin p) {K s : ℝ}
    (hc : 0 ≤ x i0 / (1 + x i0) + y i0) (hWs : 1 ≤ (W : ℝ) * s) :
    ∫ ω, transmissionRatio x y (transmissionProcess b E κ W s ω) ∂growthPathLaw W b ≤
      (growthPathLaw W b (entranceEvent b E κ K s W)).toReal +
        Real.exp (-(x i0 / (1 + x i0) + y i0) * K) := by
  set c := x i0 / (1 + x i0) + y i0
  set S := entranceEvent b E κ K s W
  set F := fun ω => transmissionRatio x y (transmissionProcess b E κ W s ω)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => (transmissionRatio_mem_vec h _).1.le
  have hpt : ∀ᵐ ω ∂growthPathLaw W b,
      ENNReal.ofReal (F ω) ≤ S.indicator 1 ω + ENNReal.ofReal (Real.exp (-c * K)) := by
    filter_upwards [mass_transmissionProcess (W := W) hκ hb hE1 hE2] with ω hω
    have hle := transmissionRatio_le_exp_mass h i0 (transmissionProcess b E κ W s ω)
    rw [hω s] at hle
    by_cases hg : conductanceOf (pathTransmission b E κ W ⌊(W : ℝ) * s⌋₊ ω) ≤ K
    · have hS : ω ∈ S := ⟨⌊(W : ℝ) * s⌋₊, Nat.le_floor (by simpa using hWs),
        by rw [mul_comm]; exact Nat.floor_le (by linarith), hg⟩
      rw [Set.indicator_of_mem hS]
      refine le_trans ?_ le_self_add
      simpa using (transmissionRatio_mem_vec h _).2
    · rw [not_le] at hg
      refine le_trans ?_ le_add_self
      refine ENNReal.ofReal_le_ofReal (hle.trans (Real.exp_le_exp.2 ?_))
      nlinarith
  have hlin : ∫⁻ ω, ENNReal.ofReal (F ω) ∂growthPathLaw W b ≤
      growthPathLaw W b S + ENNReal.ofReal (Real.exp (-c * K)) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    exact add_le_add_left (lintegral_indicator_one_le S) _
  have hfin : growthPathLaw W b S + ENNReal.ofReal (Real.exp (-c * K)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
  have hR : (growthPathLaw W b S + ENNReal.ofReal (Real.exp (-c * K))).toReal =
      (growthPathLaw W b S).toReal + Real.exp (-c * K) := by
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  by_cases hm : AEStronglyMeasurable F (growthPathLaw W b)
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hm, ← hR]
    exact ENNReal.toReal_mono hfin hlin
  · rw [integral_undef fun hi => hm hi.1]
    positivity

theorem mem_bulkInterval_half {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < (2 - |E|) / 2 ∧ E ∈ bulkInterval ((2 - |E|) / 2) := by
  have h := abs_lt.2 ⟨hE1, hE2⟩
  refine ⟨by linarith, ?_⟩
  rw [bulkInterval, Set.mem_Icc]
  constructor <;> linarith [neg_abs_le E, le_abs_self E]

theorem continuous_transmissionRatio_vec {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) :
    Continuous fun ν : FiniteMeasure unitInterval => transmissionRatio x y ν := by
  simp_rw [transmissionRatio_eq_prod h]
  exact continuous_finsetProd _ fun i _ =>
    continuous_transmissionRatio (h.1 i) (h.2 i).1 (h.2 i).2

/-- `F_{x,y}` of the single coordinate, as a test of `fdd` with `k = 1`. -/
def ratioTestVec {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) :
    BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => transmissionRatio x y (ν 0),
      (continuous_transmissionRatio_vec h).comp (continuous_apply 0)⟩ 1 fun a b => by
    have ha := transmissionRatio_mem_vec h (a 0)
    have hb := transmissionRatio_mem_vec h (b 0)
    simp only [ContinuousMap.coe_mk]
    rw [Real.dist_eq, abs_le]; constructor <;> linarith

/-- **Every subsequential limit has the entrance**, from `TransmissionEntranceBulk`. -/
theorem hasRatioEntrance_of (hEnt : TransmissionEntranceBulk) (hb : 0 < b) (hb2 : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hκ : IsAbsorptionProfile κ) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimit b E κ φ P μ) :
    HasRatioEntrance P μ := by
  intro p hp z hz
  have hr : IsRatioRange z.1 z.2 := IsRatioParameter.isRatioRange hz
  set i0 : Fin p := ⟨0, hp⟩
  set c := z.1 i0 / (1 + z.1 i0) + z.2 i0
  have hc : 0 < c := by
    have := (hz.2.2.2 i0).1; have := (hz.2.2.1 i0).le; positivity
  obtain ⟨hκI, hEI⟩ := mem_bulkInterval_half hE1 hE2
  obtain ⟨C, hC⟩ := hEnt b hb hb2 _ hκI κ hκ
  have := h.prob
  have key : ∀ s, 0 < s → s ≤ 1 → ∀ K, 0 < K →
      ∫ ω, transmissionRatio z.1 z.2 (μ s ω) ∂P ≤ |C| * (1 + K) * s + Real.exp (-c * K) := by
    intro s hs hs1 K hK
    refine le_of_forall_pos_le_add fun θ hθ => ?_
    obtain ⟨W₀, hW₀⟩ := hC K s θ hK hs hs1 hθ
    have hlim := h.fdd 1 ![s] (fun i => by fin_cases i; simpa using hs) (ratioTestVec hr)
    refine le_of_tendsto hlim ?_
    filter_upwards [hφ.eventually_ge_atTop (max W₀ ⌈1 / s⌉₊)] with n hn
    have hWs : 1 ≤ (φ n : ℝ) * s := by
      have h1 : (⌈1 / s⌉₊ : ℝ) ≤ φ n := by exact_mod_cast le_of_max_le_right hn
      have h2 : 1 / s ≤ (⌈1 / s⌉₊ : ℝ) := Nat.le_ceil _
      rw [← div_le_iff₀ hs]; linarith
    have hfin := integral_ratio_finite_le (W := φ n) (b := b) (E := E) (κ := κ) (K := K) hκ.2.1
      (by linarith) hE1 hE2 hr i0 hc.le hWs
    have hP : (growthPathLaw (φ n) b (entranceEvent b E κ K s (φ n))).toReal ≤
        |C| * (1 + K) * s + θ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity)
        ((hW₀ (φ n) (le_of_max_le_left hn) E hEI).trans (ENNReal.ofReal_le_ofReal (by
          have : C * (1 + K) * s ≤ |C| * (1 + K) * s := by
            gcongr; exact le_abs_self C
          linarith)))
    change ∫ ω, transmissionRatio z.1 z.2 (transmissionProcess b E κ (φ n) s ω)
      ∂growthPathLaw (φ n) b ≤ _
    linarith
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun s => lt_of_lt_of_le ha
    (integral_nonneg fun ω => (transmissionRatio_mem_vec hr _).1.le), fun a ha => ?_⟩
  obtain ⟨K, hK, hKa⟩ : ∃ K, 0 < K ∧ Real.exp (-c * K) < a / 2 := by
    have ht : Tendsto (fun K => Real.exp (-c * K)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hc)).congr fun K => ?_
      simp [neg_mul]
    obtain ⟨K, hK1, hK2⟩ := ((ht.eventually (gt_mem_nhds (half_pos ha))).and
      (eventually_gt_atTop 0)).exists
    exact ⟨K, hK2, hK1⟩
  have hδ : 0 < min 1 (a / (2 * ((|C| + 1) * (1 + K)))) := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  have hs1 : s ≤ 1 := hs.2.le.trans (min_le_left _ _)
  have hk := key s hs.1 hs1 K hK
  have h2 : (|C| + 1) * (1 + K) * s < a / 2 := by
    have := hs.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have h3 : |C| * (1 + K) * s ≤ (|C| + 1) * (1 + K) * s := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + K) hs.1]
  linarith

end BlockBand.Transmission.LawDuality
