module

public import BlockBand.Transmission.LawDuality.RatioForward

/-!
# `RatioDualityPrinciple`: the one-parameter kernel and its derivatives

The ratio integrand splits into one-parameter kernels,
`r_{x,y}(t) = Σ_i (ℓ(x_i, t) − ℓ(−y_i, t))` with `ℓ(x, t) = −log(1+xt)/t` (`ℓ(x, 0) = −x`)
(`ratioIntegrand_eq_sum_lker`). For a finite measure `ν` on `[0,1]` put
`A_ν(x) = ∫ ℓ(x, t) dν(t)` (`x > −1`). Then (`hasDerivAt_lkerInt`, `hasDerivAt_lkerInt1`)
* `A_ν'(x) = −∫ (1+xt)⁻¹ dν(t)`, `A_ν''(x) = ∫ t(1+xt)⁻² dν(t)`,
by differentiation under `∫ dν` with the domination `1 + xt ≥ δ` for `x ≥ δ − 1`, `t ∈ [0,1]`.
Bounds (`abs_lker_le`, `abs_lker1_le`, `abs_lker2_le`): `|ℓ| ≤ |x|/δ`, `|∂ℓ| ≤ 1/δ`,
`|∂²ℓ| ≤ 1/δ²`. Finally `F_{x,y}(ν) = exp Σ_i (A_ν(x_i) − A_ν(−y_i))`
(`transmissionRatio_eq_exp_lker`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

/-- `ℓ(x, t) = −log(1+xt)/t`, with value `−x` at `t = 0`. -/
def lker (x t : ℝ) : ℝ := if t = 0 then -x else -Real.log (1 + x * t) / t

/-- `∂_x ℓ(x, t) = −(1+xt)⁻¹`. -/
def lker1 (x t : ℝ) : ℝ := -(1 + x * t)⁻¹

/-- `∂²_x ℓ(x, t) = t(1+xt)⁻²`. -/
def lker2 (x t : ℝ) : ℝ := t * ((1 + x * t)⁻¹) ^ 2

theorem ratioIntegrand_eq_sum_lker {p : ℕ} (x y : Fin p → ℝ) (t : ℝ) :
    ratioIntegrand x y t = ∑ i, (lker (x i) t - lker (-y i) t) := by
  unfold ratioIntegrand lker
  split_ifs with h
  · simp only [neg_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 1 + -y i * t = 1 - y i * t by ring]
    ring

theorem one_add_mul_ge {δ x t : ℝ} (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    δ ≤ 1 + x * t := by
  nlinarith

theorem hasDerivAt_lker {x t : ℝ} (h : 0 < 1 + x * t) :
    HasDerivAt (fun x => lker x t) (lker1 x t) x := by
  by_cases ht : t = 0
  · subst ht
    have e : (fun x => lker x 0) = fun x => -x := funext fun x => by simp [lker]
    rw [e, show lker1 x 0 = -1 by simp [lker1]]
    exact (hasDerivAt_id x).neg
  · have e : (fun x => lker x t) = fun x => -Real.log (1 + x * t) / t :=
      funext fun x => by simp [lker, ht]
    rw [e]
    have h1 : HasDerivAt (fun x => 1 + x * t) t x := by
      simpa using ((hasDerivAt_id x).mul_const t).const_add 1
    have h2 := ((h1.log h.ne').neg).div_const t
    convert h2 using 1
    unfold lker1
    field_simp

theorem hasDerivAt_lker1 {x t : ℝ} (h : 0 < 1 + x * t) :
    HasDerivAt (fun x => lker1 x t) (lker2 x t) x := by
  have h1 : HasDerivAt (fun x => 1 + x * t) t x := by
    simpa using ((hasDerivAt_id x).mul_const t).const_add 1
  have h2 := (h1.inv h.ne').neg
  unfold lker1 lker2
  convert h2 using 1
  field_simp

theorem measurable_lker (x : ℝ) : Measurable fun t => lker x t :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_const.add (measurable_const.mul measurable_id)).log.neg.div measurable_id)

theorem measurable_lker_coe (x : ℝ) : Measurable fun t : unitInterval => lker x (t : ℝ) :=
  (measurable_lker x).comp measurable_subtype_coe

theorem measurable_lker1_coe (x : ℝ) : Measurable fun t : unitInterval => lker1 x (t : ℝ) :=
  (measurable_const.add (measurable_const.mul measurable_subtype_coe)).inv.neg

theorem measurable_lker1 (x : ℝ) : Measurable fun t => lker1 x t :=
  (measurable_const.add (measurable_const.mul measurable_id)).inv.neg

theorem measurable_lker2 (x : ℝ) : Measurable fun t => lker2 x t :=
  measurable_id.mul ((measurable_const.add (measurable_const.mul measurable_id)).inv.pow_const 2)

theorem abs_lker1_le {δ x t : ℝ} (hδ : 0 < δ) (h : δ ≤ 1 + x * t) : |lker1 x t| ≤ 1 / δ := by
  unfold lker1
  rw [abs_neg, abs_inv, abs_of_pos (hδ.trans_le h), one_div]
  exact inv_anti₀ hδ h

theorem abs_lker2_le {δ x t : ℝ} (hδ : 0 < δ) (h : δ ≤ 1 + x * t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |lker2 x t| ≤ 1 / δ ^ 2 := by
  unfold lker2
  have hp : 0 < 1 + x * t := hδ.trans_le h
  rw [abs_mul, abs_of_nonneg ht0, abs_pow, abs_inv, abs_of_pos hp, one_div, ← inv_pow]
  calc t * (1 + x * t)⁻¹ ^ 2 ≤ 1 * δ⁻¹ ^ 2 := by
        refine mul_le_mul ht1 (pow_le_pow_left₀ (inv_nonneg.2 hp.le) (inv_anti₀ hδ h) 2)
          (by positivity) zero_le_one
    _ = δ⁻¹ ^ 2 := one_mul _

theorem abs_lker_le {δ x t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : δ ≤ 1 + x * t) (ht0 : 0 ≤ t) :
    |lker x t| ≤ |x| / δ := by
  unfold lker
  split_ifs with ht
  · rw [abs_neg]; exact le_div_self (abs_nonneg x) hδ hδ1
  · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hp : 0 < 1 + x * t := hδ.trans_le h
    have hu1 := Real.log_le_sub_one_of_pos hp
    have hu2 := Real.one_sub_inv_le_log_of_pos hp
    have hlog : |Real.log (1 + x * t)| ≤ |x| * t / δ := by
      rw [abs_le]
      have hxt : |x * t| = |x| * t := by rw [abs_mul, abs_of_pos htp]
      constructor
      · -- `log(1+u) ≥ 1 - 1/(1+u) = u/(1+u) ≥ -|u|/δ`
        have e : 1 - (1 + x * t)⁻¹ = x * t / (1 + x * t) := by field_simp; ring
        rw [e] at hu2
        have : -(|x| * t / δ) ≤ x * t / (1 + x * t) := by
          rw [neg_le, ← neg_div, le_div_iff₀ hδ]
          have h3 : -(x * t) / (1 + x * t) ≤ |x| * t / (1 + x * t) :=
            div_le_div_of_nonneg_right (by linarith [neg_abs_le (x * t), hxt]) hp.le
          have h4 : |x| * t / (1 + x * t) ≤ |x| * t / δ :=
            div_le_div_of_nonneg_left (by positivity) hδ h
          calc -(x * t) / (1 + x * t) * δ ≤ |x| * t / δ * δ := by
                exact mul_le_mul_of_nonneg_right (h3.trans h4) hδ.le
            _ = |x| * t := by field_simp
        linarith
      · have : x * t ≤ |x| * t / δ := by
          rw [le_div_iff₀ hδ]
          have : |x| * t ≥ 0 := by positivity
          nlinarith [le_abs_self (x * t), hxt]
        linarith
    rw [neg_div, abs_neg, abs_div, abs_of_pos htp, div_le_iff₀ htp]
    calc |Real.log (1 + x * t)| ≤ |x| * t / δ := hlog
      _ = |x| / δ * t := by ring

/-! ## The integrated kernel -/

variable (ν : FiniteMeasure unitInterval)

/-- `A_ν(x) = ∫ ℓ(x, t) dν(t)`. -/
def lkerInt (x : ℝ) : ℝ := ∫ t, lker x (t : ℝ) ∂(ν : Measure unitInterval)

/-- `A_ν'(x) = ∫ ∂ℓ(x, t) dν(t) = −∫ (1+xt)⁻¹ dν`. -/
def lkerInt1 (x : ℝ) : ℝ := ∫ t, lker1 x (t : ℝ) ∂(ν : Measure unitInterval)

/-- `A_ν''(x) = ∫ ∂²ℓ(x, t) dν(t) = ∫ t(1+xt)⁻² dν`. -/
def lkerInt2 (x : ℝ) : ℝ := ∫ t, lker2 x (t : ℝ) ∂(ν : Measure unitInterval)

/-- The domination constant `δ(x) = min 1 ((1+x)/2)`. -/
def dom (x : ℝ) : ℝ := min 1 ((1 + x) / 2)

theorem dom_pos {x : ℝ} (hx : -1 < x) : 0 < dom x := lt_min one_pos (by linarith)

theorem dom_le_one (x : ℝ) : dom x ≤ 1 := min_le_left _ _

theorem dom_sub_one_le {x : ℝ} (hx : -1 < x) : dom x - 1 ≤ x := by
  have := min_le_right 1 ((1 + x) / 2); unfold dom; linarith

/-- On `(x−1)/2 < x'` the domination `1 + x't ≥ δ(x)` holds for `t ∈ [0,1]`. -/
theorem dom_le {x x' t : ℝ} (hx' : (x - 1) / 2 < x') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dom x ≤ 1 + x' * t :=
  one_add_mul_ge (dom_le_one x) (by have := min_le_right 1 ((1 + x) / 2); unfold dom; linarith)
    ht0 ht1

theorem integrable_lker {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) :
    Integrable (fun t : unitInterval => lker x (t : ℝ)) (ν : Measure unitInterval) :=
  Integrable.of_bound ((measurable_lker x).comp measurable_subtype_coe).aestronglyMeasurable
    (|x| / δ) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact abs_lker_le hδ hδ1 (one_add_mul_ge hδ1 hx t.2.1 t.2.2) t.2.1)

theorem integrable_lker1 {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) :
    Integrable (fun t : unitInterval => lker1 x (t : ℝ)) (ν : Measure unitInterval) :=
  Integrable.of_bound ((measurable_lker1 x).comp measurable_subtype_coe).aestronglyMeasurable
    (1 / δ) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_lker1_le hδ (one_add_mul_ge hδ1 hx t.2.1 t.2.2))

theorem hasDerivAt_lkerInt {x : ℝ} (hx : -1 < x) :
    HasDerivAt (lkerInt ν) (lkerInt1 ν x) x := by
  have hs : Ioi ((x - 1) / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  have hδ := dom_pos hx
  have hx0 : dom x - 1 ≤ x := dom_sub_one_le hx
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (t : unitInterval) => lker x (t : ℝ))
    (F' := fun x (t : unitInterval) => lker1 x (t : ℝ)) (bound := fun _ => 1 / dom x) hs
    (Eventually.of_forall fun x' => (measurable_lker_coe x').aestronglyMeasurable)
    (integrable_lker ν hδ (dom_le_one x) hx0)
    ((measurable_lker1 x).comp measurable_subtype_coe).aestronglyMeasurable
    (Eventually.of_forall fun t x' hx' => ?_) (integrable_const _)
    (Eventually.of_forall fun t x' hx' => ?_)).2
  · rw [Real.norm_eq_abs]; exact abs_lker1_le hδ (dom_le hx' t.2.1 t.2.2)
  · exact hasDerivAt_lker (hδ.trans_le (dom_le hx' t.2.1 t.2.2))

theorem hasDerivAt_lkerInt1 {x : ℝ} (hx : -1 < x) :
    HasDerivAt (lkerInt1 ν) (lkerInt2 ν x) x := by
  have hs : Ioi ((x - 1) / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  have hδ := dom_pos hx
  have hx0 : dom x - 1 ≤ x := dom_sub_one_le hx
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (t : unitInterval) => lker1 x (t : ℝ))
    (F' := fun x (t : unitInterval) => lker2 x (t : ℝ)) (bound := fun _ => 1 / dom x ^ 2) hs
    (Eventually.of_forall fun x' => (measurable_lker1_coe x').aestronglyMeasurable)
    (integrable_lker1 ν hδ (dom_le_one x) hx0)
    ((measurable_lker2 x).comp measurable_subtype_coe).aestronglyMeasurable
    (Eventually.of_forall fun t x' hx' => ?_) (integrable_const _)
    (Eventually.of_forall fun t x' hx' => ?_)).2
  · rw [Real.norm_eq_abs]; exact abs_lker2_le hδ (dom_le hx' t.2.1 t.2.2) t.2.1 t.2.2
  · exact hasDerivAt_lker1 (hδ.trans_le (dom_le hx' t.2.1 t.2.2))

/-- **`F_{x,y}(ν) = exp Σ_i (A_ν(x_i) − A_ν(−y_i))`** for `x > −1`, `y < 1`. -/
theorem transmissionRatio_eq_exp_lker {p : ℕ} {x y : Fin p → ℝ} (hx : ∀ i, -1 < x i)
    (hy : ∀ i, y i < 1) :
    transmissionRatio x y ν = Real.exp (∑ i, (lkerInt ν (x i) - lkerInt ν (-y i))) := by
  unfold transmissionRatio
  congr 1
  simp_rw [ratioIntegrand_eq_sum_lker]
  have hi : ∀ z : ℝ, -1 < z → Integrable (fun t : unitInterval => lker z (t : ℝ))
      (ν : Measure unitInterval) := fun z hz =>
    integrable_lker ν (dom_pos hz) (dom_le_one z) (dom_sub_one_le hz)
  rw [integral_finsetSum (μ := (ν : Measure unitInterval)) Finset.univ
    (f := fun i (t : unitInterval) => lker (x i) (t : ℝ) - lker (-y i) (t : ℝ))
    fun i _ => (hi _ (hx i)).sub (hi _ (by linarith [hy i]))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_sub (hi _ (hx i)) (hi _ (by linarith [hy i]))

end BlockBand.Transmission.LawDuality
