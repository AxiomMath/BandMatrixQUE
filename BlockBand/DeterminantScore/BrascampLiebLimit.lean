module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Brascamp–Lieb: passage from an exhaustion to the whole domain

* `evariance_le_lintegral_sq`: `Var g ≤ E (g - c)²` for every real `c` (probability measure,
  `g` measurable, no integrability assumption).
* `exists_center_lintegral_le`: if `A_n ↑` cover almost everything, `g` is bounded on some
  `A_{n₀}` of positive finite measure, and for each `n` some centre `c_n` gives
  `∫_{A_n} (g - c_n)² ≤ V < ∞`, then `∫ (g - c)² ≤ V` for some `c` (bounded centres,
  Bolzano–Weierstrass, Fatou).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Var g ≤ E (g - c)²` for every centre `c`. -/
theorem evariance_le_lintegral_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Measurable g) (c : ℝ) :
    evariance g μ ≤ ∫⁻ x, ENNReal.ofReal ((g x - c) ^ 2) ∂μ := by
  by_cases h : ∫⁻ x, ENNReal.ofReal ((g x - c) ^ 2) ∂μ = ⊤
  · rw [h]; exact le_top
  have hm : Measurable fun x => g x - c := hg.sub_const c
  have hi : Integrable (fun x => (g x - c) ^ 2) μ := by
    refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have : (fun x => ‖(g x - c) ^ 2‖ₑ) = fun x => ENNReal.ofReal ((g x - c) ^ 2) := by
      funext x; exact Real.enorm_of_nonneg (sq_nonneg _)
    rw [this]
    exact lt_top_iff_ne_top.2 h
  have hL : MemLp (fun x => g x - c) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi
  have hL' : MemLp g 2 μ := by
    have h1 := hL.add (memLp_const c)
    have h2 : ((fun x => g x - c) + fun _ => c) = g := by funext x; simp
    rwa [h2] at h1
  rw [← hL'.ofReal_variance_eq, ← variance_sub_const hg.aestronglyMeasurable c,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (variance_le_expectation_sq hm.aestronglyMeasurable)

/-- **Exhaustion step.** -/
theorem exists_center_lintegral_le {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : Measurable g) {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcov : ∀ᵐ x ∂μ, ∃ n, x ∈ A n) {V : ℝ≥0∞} (hV : V ≠ ⊤) {n₀ : ℕ} (h0 : μ (A n₀) ≠ 0)
    {B : ℝ} (hB : ∀ x ∈ A n₀, |g x| ≤ B)
    (hc : ∀ n, ∃ c : ℝ, ∫⁻ x in A n, ENNReal.ofReal ((g x - c) ^ 2) ∂μ ≤ V) :
    ∃ c : ℝ, ∫⁻ x, ENNReal.ofReal ((g x - c) ^ 2) ∂μ ≤ V := by
  choose c hcV using hc
  set W := V / μ (A n₀) with hW
  have hWt : W ≠ ⊤ := ENNReal.div_ne_top hV h0
  -- the centres are bounded from `n₀` on
  have hbd : ∀ n, n₀ ≤ n → |c n| ≤ B + W.toReal + 1 := by
    intro n hn
    by_contra hlt
    have hlt' : B + W.toReal + 1 < |c n| := not_le.1 hlt
    set β := |c n| - B with hβ
    have hβ1 : W.toReal + 1 < β := by rw [hβ]; linarith
    have hpt : ∀ x ∈ A n₀, ENNReal.ofReal (β ^ 2) ≤ ENNReal.ofReal ((g x - c n) ^ 2) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have h1 : β ≤ |g x - c n| := by
        have := abs_sub_abs_le_abs_sub (c n) (g x)
        rw [abs_sub_comm] at this
        have := hB x hx
        rw [hβ]; linarith
      have hβ0 : 0 ≤ β := by linarith [ENNReal.toReal_nonneg (a := W)]
      rw [← sq_abs (g x - c n)]
      exact pow_le_pow_left₀ hβ0 h1 2
    have hlow : μ (A n₀) * ENNReal.ofReal (β ^ 2) ≤ V := by
      calc μ (A n₀) * ENNReal.ofReal (β ^ 2) = ∫⁻ _x in A n₀, ENNReal.ofReal (β ^ 2) ∂μ := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ x in A n₀, ENNReal.ofReal ((g x - c n) ^ 2) ∂μ :=
            setLIntegral_mono ((hg.sub_const _).pow_const 2).ennreal_ofReal hpt
        _ ≤ ∫⁻ x in A n, ENNReal.ofReal ((g x - c n) ^ 2) ∂μ :=
            lintegral_mono_set (hmono hn)
        _ ≤ V := hcV n
    have hle : ENNReal.ofReal (β ^ 2) ≤ W := by
      rw [hW, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top _ _)), mul_comm]
      exact hlow
    have := (ENNReal.ofReal_le_iff_le_toReal hWt).1 hle
    nlinarith [ENNReal.toReal_nonneg (a := W)]
  -- Bolzano–Weierstrass
  set d : ℕ → ℝ := fun k => c (n₀ + k) with hd
  obtain ⟨c₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := d)
    (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := B + W.toReal + 1))
    (fun k => by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact hbd _ (Nat.le_add_right _ _))
  refine ⟨c₀, ?_⟩
  set F : ℕ → Ω → ℝ≥0∞ := fun k => (A (n₀ + φ k)).indicator
    (fun x => ENNReal.ofReal ((g x - d (φ k)) ^ 2)) with hF
  have hFm : ∀ k, Measurable (F k) := fun k =>
    ((hg.sub_const _).pow_const 2).ennreal_ofReal.indicator (hA _)
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal ((g x - c₀) ^ 2) = liminf (fun k => F k x) atTop := by
    filter_upwards [hcov] with x ⟨n, hn⟩
    have hev : ∀ᶠ k in atTop, F k x = ENNReal.ofReal ((g x - d (φ k)) ^ 2) := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have : x ∈ A (n₀ + φ k) :=
        hmono (hk.trans ((hφ.id_le k).trans (Nat.le_add_left _ _))) hn
      simp only [hF, Set.indicator_of_mem this]
    have ht : Tendsto (fun k => F k x) atTop (𝓝 (ENNReal.ofReal ((g x - c₀) ^ 2))) := by
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_const_nhds.sub hlim).pow 2))
    exact ht.liminf_eq.symm
  calc ∫⁻ x, ENNReal.ofReal ((g x - c₀) ^ 2) ∂μ = ∫⁻ x, liminf (fun k => F k x) atTop ∂μ :=
        lintegral_congr_ae hpt
    _ ≤ liminf (fun k => ∫⁻ x, F k x ∂μ) atTop := lintegral_liminf_le hFm
    _ ≤ V := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
        rw [hF, lintegral_indicator (hA _)]
        exact hcV _

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
