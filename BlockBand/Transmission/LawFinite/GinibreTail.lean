module

public import BlockBand.Transmission.LawFinite.GinibreColumn
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lower tail of a Ginibre column's partial mass (chi-square Chernoff bound)

For `g ~ colLaw W t` and `1 ≤ k ≤ W` put `S_k = Σ_{l<k} |g_l|²` (a `Gamma(k, t)` variable).
* `integral_exp_chiSum`: `E e^{-sS_k} = (1+st)^{-k}` (`s ≥ 0`);
* `colLaw_chiSum_lt`: `P(S_k < x t k) ≤ (e x)^k` for `0 < x ≤ 1` (Chernoff);
* **`lintegral_nlog_chiSum_le`**: `E log⁻-type(S_k/(tk)) ≤ 3`, with `nlog y = -log y` for
  `y > 0` and `nlog y = ∞` for `y ≤ 0` (so the bound also gives `S_k > 0` a.s.).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

variable {W : ℕ}

/-- `(E e^{-sX²})² = (1+2sv)⁻¹` for `X ~ N(0,v)`, `v > 0`, `s ≥ 0`. -/
theorem gauss_exp_sq_sq {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s * x ^ 2) ∂gaussianReal 0 v) ^ 2 = (1 + 2 * s * v)⁻¹ := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  rw [integral_gaussianReal_eq_integral_smul hv]
  have h1 : (fun x : ℝ => gaussianPDFReal 0 v x • Real.exp (-s * x ^ 2)) =
      fun x => (√(2 * π * v))⁻¹ * Real.exp (-(s + 1 / (2 * v)) * x ^ 2) := by
    funext x
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [h1, integral_const_mul, integral_gaussian, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- `S_k = Σ_{l<k} |g_l|²`. -/
def chiSum (k : ℕ) (g : Fin W → ℂ) : ℝ := ∑ l : Fin W, if l.val < k then ‖g l‖ ^ 2 else 0

theorem continuous_chiSum (k : ℕ) : Continuous (chiSum (W := W) k) := by
  unfold chiSum
  refine continuous_finsetSum _ fun l _ => ?_
  split_ifs
  · exact (continuous_norm.comp (continuous_apply l)).pow 2
  · exact continuous_const

theorem chiSum_nonneg (k : ℕ) (g : Fin W → ℂ) : 0 ≤ chiSum k g :=
  Finset.sum_nonneg fun l _ => by split_ifs <;> positivity

theorem chiSum_toC (k : ℕ) (r : Fin W × Fin 2 → ℝ) :
    chiSum k (toC r) = ∑ p : Fin W × Fin 2, if p.1.val < k then r p ^ 2 else 0 := by
  rw [chiSum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.sum_univ_two]
  split_ifs
  · simp only [toC]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  · simp

theorem card_filter_lt (k : ℕ) (hk : k ≤ W) :
    (Finset.univ.filter fun l : Fin W => l.val < k).card = k := by
  have : (Finset.univ.filter fun l : Fin W => l.val < k) =
      (Finset.range k).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hk) := by
    ext l; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- `E e^{-sS_k} = (1+st)^{-k}`. -/
theorem integral_exp_chiSum {t : ℝ≥0} (ht : t ≠ 0) {k : ℕ} (hk : k ≤ W) {s : ℝ} (hs : 0 ≤ s) :
    ∫ g, Real.exp (-s * chiSum k g) ∂colLaw W t = ((1 + s * t)⁻¹) ^ k := by
  have hv : t / 2 ≠ 0 := by simpa using ht
  have hc : Continuous fun g : Fin W → ℂ => Real.exp (-s * chiSum k g) :=
    continuous_exp.comp (continuous_const.mul (continuous_chiSum k))
  rw [colLaw, integral_map measurable_toC.aemeasurable hc.aestronglyMeasurable]
  set f : Fin W × Fin 2 → ℝ → ℝ := fun p y => if p.1.val < k then Real.exp (-s * y ^ 2) else 1
  have hprod : ∀ r : Fin W × Fin 2 → ℝ,
      Real.exp (-s * chiSum k (toC r)) = ∏ p, f p (r p) := by
    intro r
    rw [chiSum_toC, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [f]
    split_ifs <;> simp
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod, Fintype.prod_prod_type]
  have hI := gauss_exp_sq_sq hv hs
  have : ∀ x : Fin W, ∏ c : Fin 2, ∫ y, f (x, c) y ∂gaussianReal 0 (t / 2) =
      if x.val < k then (1 + s * t)⁻¹ else 1 := by
    intro x
    rw [Fin.prod_univ_two]
    simp only [f]
    split_ifs
    · rw [← sq, hI]
      congr 2
      push_cast
      ring
    · simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, card_filter_lt k hk]

/-- **Chernoff**: `P(S_k < x t k) ≤ (e x)^k` for `0 < x ≤ 1`. -/
theorem colLaw_chiSum_lt {t : ℝ≥0} (ht : t ≠ 0) {k : ℕ} (hk : k ≤ W) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) :
    colLaw W t {g | chiSum k g < x * t * k} ≤ ENNReal.ofReal ((Real.exp 1 * x) ^ k) := by
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.1 h.symm))
  set s : ℝ := (1 / x - 1) / t
  have hs : 0 ≤ s := div_nonneg (by rw [sub_nonneg, le_div_iff₀ hx0]; linarith) ht0.le
  have hst : 1 + s * t = 1 / x := by simp only [s]; field_simp; ring
  set c : ℝ := x * t * k
  set F : (Fin W → ℂ) → ℝ := fun g => Real.exp (-s * chiSum k g)
  have hFc : Continuous F := continuous_exp.comp (continuous_const.mul (continuous_chiSum k))
  have hsub : {g | chiSum k g < c} ⊆
      {g | ENNReal.ofReal (Real.exp (-s * c)) ≤ ENNReal.ofReal (F g)} := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    nlinarith
  have hpos : 0 < Real.exp (-s * c) := Real.exp_pos _
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
    (hFc.measurable.ennreal_ofReal.aemeasurable) (by simpa using hpos) ENNReal.ofReal_ne_top).trans ?_)
  have hint : Integrable F (colLaw W t) :=
    Integrable.of_bound hFc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      nlinarith [chiSum_nonneg k g])
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le),
    integral_exp_chiSum ht hk hs, ← ENNReal.ofReal_div_of_pos hpos]
  apply ENNReal.ofReal_le_ofReal
  rw [hst, one_div, inv_inv, div_eq_mul_inv, ← Real.exp_neg, neg_mul, neg_neg, mul_pow]
  have hsc : s * c = (1 - x) * k := by
    simp only [s, c]; field_simp
  rw [hsc, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0.le _)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `nlog y = -log y` for `y > 0` and `∞` for `y ≤ 0` (an antitone `log⁻`-type weight). -/
def nlog (y : ℝ) : ℝ≥0∞ := if 0 < y then ENNReal.ofReal (-Real.log y) else ⊤

theorem nlog_antitone {y z : ℝ} (h : y ≤ z) : nlog z ≤ nlog y := by
  unfold nlog
  by_cases hy : 0 < y
  · simp only [hy, lt_of_lt_of_le hy h, ↓reduceIte]
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log hy h))
  · simp only [hy, ↓reduceIte]; exact le_top

/-- `nlog y ≤ Σ_n 1{y < e^{-n}}`. -/
theorem nlog_le_tsum (y : ℝ) :
    nlog y ≤ ∑' n : ℕ, ({z : ℝ | z < Real.exp (-(n : ℝ))}.indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  unfold nlog
  by_cases hy : 0 < y
  · simp only [hy, ↓reduceIte]
    set N := ⌈-Real.log y⌉₊
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range N))
    have : ∀ n ∈ Finset.range N,
        ({z : ℝ | z < Real.exp (-(n : ℝ))}.indicator (fun _ => (1 : ℝ≥0∞)) y) = 1 := by
      intro n hn
      rw [Set.indicator_of_mem]
      simp only [Set.mem_ofPred_eq]
      have h1 : (n : ℝ) < -Real.log y := Nat.lt_ceil.1 (Finset.mem_range.1 hn)
      rw [← Real.exp_log hy]
      exact Real.exp_lt_exp.2 (by linarith)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
  · simp only [hy, ↓reduceIte]
    have : ∀ n : ℕ, ({z : ℝ | z < Real.exp (-(n : ℝ))}.indicator (fun _ => (1 : ℝ≥0∞)) y) = 1 :=
      fun n => Set.indicator_of_mem (s := {z : ℝ | z < Real.exp (-(n : ℝ))}) (a := y)
        (lt_of_le_of_lt (not_lt.1 hy) (Real.exp_pos _)) _
    simp_rw [this]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

/-- **`E nlog(S_k/(tk)) ≤ 3`** for `1 ≤ k ≤ W`. -/
theorem lintegral_nlog_chiSum_le {t : ℝ≥0} (ht : t ≠ 0) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ W) :
    ∫⁻ g, nlog (chiSum k g / (t * k)) ∂colLaw W t ≤ 3 := by
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.1 h.symm))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  set μ := colLaw W t
  set A : ℕ → Set (Fin W → ℂ) := fun n => {g | chiSum k g < Real.exp (-(n : ℝ)) * t * k}
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_lt (continuous_chiSum k).measurable measurable_const
  have hpt : ∀ g, nlog (chiSum k g / (t * k)) ≤ ∑' n : ℕ, (A n).indicator (fun _ => 1) g := by
    intro g
    refine (nlog_le_tsum _).trans (ENNReal.tsum_le_tsum fun n => ?_)
    by_cases hg : chiSum k g / (t * k) < Real.exp (-(n : ℝ))
    · rw [Set.indicator_of_mem (show chiSum k g / (t * k) ∈ {z : ℝ | z < Real.exp (-(n : ℝ))}
        from hg), Set.indicator_of_mem]
      simp only [A, Set.mem_ofPred_eq]
      rw [div_lt_iff₀ (mul_pos ht0 hk0)] at hg
      linarith
    · rw [Set.indicator_of_notMem (show chiSum k g / (t * k) ∉ {z : ℝ | z < Real.exp (-(n : ℝ))}
        from hg)]
      exact bot_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun n => (measurable_const.indicator (hA n)).aemeasurable]
  simp_rw [lintegral_indicator_const (hA _), one_mul]
  have hbd : ∀ n : ℕ, μ (A (n + 1)) ≤ ENNReal.ofReal (Real.exp (-1)) ^ n := by
    intro n
    have hx0 : 0 < Real.exp (-((n + 1 : ℕ) : ℝ)) := Real.exp_pos _
    have hx1 : Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
    refine (colLaw_chiSum_lt ht hk hx0 hx1).trans ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp 1 * Real.exp (-((n + 1 : ℕ) : ℝ)) = Real.exp (-1) ^ n := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he]
    have h0 : 0 ≤ Real.exp (-1) ^ n := pow_nonneg (Real.exp_pos _).le _
    have h1 : Real.exp (-1) ^ n ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.2 (by norm_num))
    calc (Real.exp (-1) ^ n) ^ k ≤ (Real.exp (-1) ^ n) ^ 1 := pow_le_pow_of_le_one h0 h1 hk1
      _ = _ := pow_one _
  rw [tsum_eq_zero_add' ENNReal.summable]
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1))
  have hr : r ≤ 1 / 2 := by
    have : Real.exp (-1) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    calc r ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal this
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hgeo : (∑' n : ℕ, r ^ n) ≤ 2 := by
    rw [ENNReal.tsum_geometric]
    have h1 : 1 / 2 ≤ 1 - r := by
      apply ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top
      calc r + 1 / 2 ≤ 1 / 2 + 1 / 2 := add_le_add hr le_rfl
        _ = 1 := ENNReal.add_halves 1
    calc (1 - r)⁻¹ ≤ (1 / 2)⁻¹ := ENNReal.inv_le_inv.2 h1
      _ = 2 := by simp
  calc μ (A 0) + ∑' n : ℕ, μ (A (n + 1)) ≤ 1 + 2 :=
        add_le_add prob_le_one ((ENNReal.tsum_le_tsum hbd).trans hgeo)
    _ = 3 := by norm_num

end BlockBand.Transmission.LawFinite
