module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Chernoff tails of linear forms of a Gaussian product

Law: `gaussPi κ v = Π_k N(0, v)` on `κ → ℝ` (`κ` finite).

* `mgf_linear`: `E exp(t Σ a_k ρ_k) = exp(v t² Σ a_k² / 2)`.
* `measure_linear_ge`: `P(Σ a_k ρ_k ≥ r) ≤ exp(-r²/(2s))` if `vΣa_k² ≤ s`, `s > 0`, `r ≥ 0`.
* `measure_complex_linear_gt`: `P(|Σ ρ_k c_k| > r) ≤ 4 exp(-r²/(4s))` if `vΣ|c_k|² ≤ s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

variable {κ : Type*} [Fintype κ]

/-- The centered Gaussian product law with common variance `v`. -/
abbrev gaussPi (κ : Type*) [Fintype κ] (v : ℝ≥0) : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 v

theorem exp_linear_eq (a : κ → ℝ) (t : ℝ) (ρ : κ → ℝ) :
    exp (t * ∑ k, a k * ρ k) = ∏ k, exp ((t * a k) * ρ k) := by
  rw [Finset.mul_sum, Real.exp_sum]
  congr 1; ext k; ring_nf

theorem integrable_exp_linear (v : ℝ≥0) (a : κ → ℝ) (t : ℝ) :
    Integrable (fun ρ => exp (t * ∑ k, a k * ρ k)) (gaussPi κ v) := by
  simp_rw [exp_linear_eq]
  exact Integrable.fintype_prod (f := fun k x => exp ((t * a k) * x))
    fun k => integrable_exp_mul_gaussianReal _

theorem mgf_linear (v : ℝ≥0) (a : κ → ℝ) (t : ℝ) :
    mgf (fun ρ => ∑ k, a k * ρ k) (gaussPi κ v) t = exp (v * t ^ 2 * (∑ k, a k ^ 2) / 2) := by
  rw [mgf]
  simp_rw [exp_linear_eq]
  rw [integral_fintype_prod_eq_prod (f := fun k x => exp ((t * a k) * x))]
  have h : ∀ k, ∫ x, exp ((t * a k) * x) ∂gaussianReal 0 v = exp (v * (t * a k) ^ 2 / 2) := by
    intro k
    have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) (t * a k)
    simpa [mgf] using this
  simp_rw [h, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  congr 1; ext k; ring

theorem real_measure_linear_ge (v : ℝ≥0) (a : κ → ℝ) {s r : ℝ} (hs : 0 < s)
    (hvs : v * ∑ k, a k ^ 2 ≤ s) (hr : 0 ≤ r) :
    (gaussPi κ v).real {ρ | r ≤ ∑ k, a k * ρ k} ≤ exp (-(r ^ 2 / (2 * s))) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussPi κ v) (X := fun ρ => ∑ k, a k * ρ k) r
    (t := r / s) (by positivity) (integrable_exp_linear v a _)
  rw [mgf_linear] at h
  refine h.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (v : ℝ) * (r / s) ^ 2 * (∑ k, a k ^ 2) / 2 ≤ s * (r / s) ^ 2 / 2 := by
    have : (v : ℝ) * (r / s) ^ 2 * (∑ k, a k ^ 2) = (r / s) ^ 2 * ((v : ℝ) * ∑ k, a k ^ 2) := by
      ring
    rw [this]
    have h0 : 0 ≤ (r / s) ^ 2 := by positivity
    nlinarith
  have h2 : s * (r / s) ^ 2 / 2 = r ^ 2 / (2 * s) := by field_simp
  have h3 : -(r / s) * r = -(2 * (r ^ 2 / (2 * s))) := by field_simp
  linarith

theorem measure_linear_ge (v : ℝ≥0) (a : κ → ℝ) {s r : ℝ} (hs : 0 < s)
    (hvs : v * ∑ k, a k ^ 2 ≤ s) (hr : 0 ≤ r) :
    gaussPi κ v {ρ | r ≤ ∑ k, a k * ρ k} ≤ ENNReal.ofReal (exp (-(r ^ 2 / (2 * s)))) := by
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (real_measure_linear_ge v a hs hvs hr)

/-- Tail of a complex linear form `Σ_k ρ_k c_k` of the Gaussian product. -/
theorem measure_complex_linear_gt (v : ℝ≥0) (c : κ → ℂ) {s r : ℝ} (hs : 0 < s)
    (hvs : v * ∑ k, ‖c k‖ ^ 2 ≤ s) (hr : 0 ≤ r) :
    gaussPi κ v {ρ | r < ‖∑ k, (ρ k : ℂ) * c k‖} ≤
      4 * ENNReal.ofReal (exp (-(r ^ 2 / (4 * s)))) := by
  set q := r / Real.sqrt 2
  have hq : 0 ≤ q := by positivity
  have hq2 : q ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hre : ∀ ρ : κ → ℝ, (∑ k, (ρ k : ℂ) * c k).re = ∑ k, (c k).re * ρ k := by
    intro ρ; rw [Complex.re_sum]; congr 1; ext k; simp [mul_comm]
  have him : ∀ ρ : κ → ℝ, (∑ k, (ρ k : ℂ) * c k).im = ∑ k, (c k).im * ρ k := by
    intro ρ; rw [Complex.im_sum]; congr 1; ext k; simp [mul_comm]
  have hsub : {ρ : κ → ℝ | r < ‖∑ k, (ρ k : ℂ) * c k‖} ⊆
      ({ρ | q ≤ ∑ k, (c k).re * ρ k} ∪ {ρ | q ≤ ∑ k, (-(c k).re) * ρ k}) ∪
      ({ρ | q ≤ ∑ k, (c k).im * ρ k} ∪ {ρ | q ≤ ∑ k, (-(c k).im) * ρ k}) := by
    intro ρ hρ
    simp only [Set.mem_ofPred_eq] at hρ
    simp only [Set.mem_union, Set.mem_ofPred_eq, neg_mul, Finset.sum_neg_distrib]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
    set z := ∑ k, (ρ k : ℂ) * c k
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← hre] at h1 h2; rw [← him] at h3 h4
    have : z.re ^ 2 < q ^ 2 := by nlinarith
    have : z.im ^ 2 < q ^ 2 := by nlinarith
    have : ‖z‖ ^ 2 < r ^ 2 := by nlinarith
    nlinarith [norm_nonneg z]
  have hbound : ∀ a : κ → ℝ, (∀ k, a k ^ 2 ≤ ‖c k‖ ^ 2) →
      gaussPi κ v {ρ | q ≤ ∑ k, a k * ρ k} ≤ ENNReal.ofReal (exp (-(r ^ 2 / (4 * s)))) := by
    intro a ha
    have hva : (v : ℝ) * ∑ k, a k ^ 2 ≤ s :=
      le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ha k) v.2) hvs
    refine (measure_linear_ge v a hs hva hq).trans (le_of_eq ?_)
    congr 2; rw [hq2]; field_simp; ring
  have hre2 : ∀ k, (c k).re ^ 2 ≤ ‖c k‖ ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (c k).im]
  have him2 : ∀ k, (c k).im ^ 2 ≤ ‖c k‖ ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (c k).re]
  calc gaussPi κ v {ρ | r < ‖∑ k, (ρ k : ℂ) * c k‖}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) (measure_union_le _ _)
    _ ≤ _ := add_le_add (add_le_add (hbound _ hre2) (hbound _ fun k => by simpa using hre2 k))
        (add_le_add (hbound _ him2) (hbound _ fun k => by simpa using him2 k))
    _ = _ := by ring

end BlockBand.Transmission.PassiveLayer
