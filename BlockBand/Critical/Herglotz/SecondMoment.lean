module

public import BlockBand.Critical.Herglotz.SineIntensity
public import BlockBand.Critical.Herglotz.SinePair

/-!
# Second moment of decorated sine linear statistics

For the decorated sine process with mark law `γ` and a nonnegative compactly supported continuous
test `f`, the linear statistic `X_f = Σ f(x_j, g_j)` has
`E X_f² = ∫ x, ∫ g, f(x, g)² dγ dx + ∫∫ (1 - K(x,y)²) a(x) a(y) dx dy`, `K = sineKernel`,
`a(x) = ∫ f(x, g) dγ(g)`.

* `exp_neg_sub_one_add_mem`, `exp_neg_quot_two_mem`, `tendsto_exp_neg_quot_two` — elementary.
* `lintegral_sq_half_eq_of_tendsto` — abstract second-moment step.
* `tendsto_decoratedSineLaplace_quot_two` — second-order Fredholm expansion.
* `lintegral_sq_coordinate_of_decoratedSine` — **second moment** for nonnegative `C_c` tests.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Endpoints (intensityStep intensityStep_pos intensityStep_le_one
  tendsto_intensityStep one_sub_exp_neg_mem one_sub_exp_div_mem tendsto_one_sub_exp_div
  fredholmSeries fredholmIntegral abs_fredholmSeries_sub_sum_le sum_range_three_fredholmTerm
  abs_det_sineKernel_le_one sineKernel_self)

/-!
## Elementary second-order bounds
-/

/-- `0 ≤ e^{-u} - 1 + u ≤ u²/2` for `u ≥ 0`. -/
theorem exp_neg_sub_one_add_mem {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.exp (-u) - 1 + u ∧ Real.exp (-u) - 1 + u ≤ u ^ 2 / 2 := by
  refine ⟨by linarith [Real.add_one_le_exp (-u)], ?_⟩
  have h1 := Real.quadratic_le_exp_of_nonneg hu
  have hpos := Real.exp_pos (-u)
  have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hA : 0 < 1 + u + u ^ 2 / 2 := by positivity
  have h3 : Real.exp (-u) * (1 + u + u ^ 2 / 2) ≤
      (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) := by
    calc Real.exp (-u) * (1 + u + u ^ 2 / 2) ≤ Real.exp (-u) * Real.exp u :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = 1 := h2
      _ ≤ _ := by nlinarith [pow_nonneg hu 4]
  have := le_of_mul_le_mul_right h3 hA
  linarith

/-- `0 ≤ (e^{-tu} - 1 + tu)/t² ≤ u²/2` for `u ≥ 0`, `t > 0`. -/
theorem exp_neg_quot_two_mem {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    0 ≤ (Real.exp (-(t * u)) - 1 + t * u) / t ^ 2 ∧
      (Real.exp (-(t * u)) - 1 + t * u) / t ^ 2 ≤ u ^ 2 / 2 := by
  have h := exp_neg_sub_one_add_mem (mul_nonneg ht.le hu)
  refine ⟨div_nonneg h.1 (by positivity), ?_⟩
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ (t * u) ^ 2 / 2 := h.2
    _ = u ^ 2 / 2 * t ^ 2 := by ring

/-- `(e^{-t_n u} - 1 + t_n u)/t_n² → u²/2` along `t_n = intensityStep n = 1/(n+1)`. -/
theorem tendsto_exp_neg_quot_two {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => (Real.exp (-(intensityStep n * u)) - 1 + intensityStep n * u) /
      intensityStep n ^ 2) atTop (𝓝 (u ^ 2 / 2)) := by
  set t := intensityStep with ht
  have hlim : Tendsto (fun n => t n * u) atTop (𝓝 0) := by
    simpa using tendsto_intensityStep.mul_const u
  have hev : ∀ᶠ n in atTop, t n * u ≤ 1 := hlim.eventually (ge_mem_nhds zero_lt_one)
  have hbound : ∀ᶠ n in atTop,
      ‖(Real.exp (-(t n * u)) - 1 + t n * u) / t n ^ 2 - u ^ 2 / 2‖ ≤ t n * u ^ 3 := by
    filter_upwards [hev] with n hn
    have htn : 0 < t n := intensityStep_pos n
    have h0 : 0 ≤ t n * u := mul_nonneg htn.le hu
    have hx : |(-(t n * u))| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact hn
    have he := Real.exp_bound hx (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, (-(t n * u)) ^ m / (Nat.factorial m : ℝ) =
        1 - t n * u + (t n * u) ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
      ring
    rw [hs, abs_neg, abs_of_nonneg h0] at he
    have hid : (Real.exp (-(t n * u)) - 1 + t n * u) / t n ^ 2 - u ^ 2 / 2 =
        (Real.exp (-(t n * u)) - (1 - t n * u + (t n * u) ^ 2 / 2)) / t n ^ 2 := by
      field_simp
      ring
    rw [hid, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < t n ^ 2),
      div_le_iff₀ (by positivity)]
    have he' : |Real.exp (-(t n * u)) - (1 - t n * u + (t n * u) ^ 2 / 2)| ≤
        (t n * u) ^ 3 * (2 / 9) := by
      convert he using 2
      norm_num [Nat.factorial]
    refine he'.trans ?_
    have : 0 ≤ t n * u ^ 3 * t n ^ 2 := by positivity
    nlinarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  simpa using tendsto_intensityStep.mul_const (u ^ 3)

/-!
## The abstract second-moment step
-/

/-- **Second moment from second-order Laplace quotients.** For `Λ ≥ 0` measurable and
integrable on a probability space, if `(E e^{-t_n Λ} - 1 + t_n E Λ)/t_n² → H` along
`t_n = 1/(n+1)`, then `∫⁻ ofReal (Λ²/2) = ofReal H` (Fatou for `≤`, the bound
`(e^{-tΛ} - 1 + tΛ)/t² ≤ Λ²/2` for `≥`). -/
theorem lintegral_sq_half_eq_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Λ : Ω → ℝ} (hΛm : Measurable Λ) (hΛ0 : ∀ ω, 0 ≤ Λ ω)
    (hΛi : Integrable Λ P) {H : ℝ}
    (hH : Tendsto (fun n => (∫ ω, Real.exp (-(intensityStep n * Λ ω)) ∂P - 1 +
      intensityStep n * ∫ ω, Λ ω ∂P) / intensityStep n ^ 2) atTop (𝓝 H)) :
    ∫⁻ ω, ENNReal.ofReal (Λ ω ^ 2 / 2) ∂P = ENNReal.ofReal H := by
  set t := intensityStep with ht
  set f : ℕ → Ω → ℝ := fun n ω =>
    (Real.exp (-(t n * Λ ω)) - 1 + t n * Λ ω) / t n ^ 2 with hf
  have hem (n : ℕ) : Measurable fun ω => Real.exp (-(t n * Λ ω)) :=
    Real.measurable_exp.comp ((hΛm.const_mul _).neg)
  have hfm (n : ℕ) : Measurable (f n) :=
    ((((hem n).sub_const 1).add (hΛm.const_mul _))).div_const _
  have hfmem (n : ℕ) (ω : Ω) := exp_neg_quot_two_mem (hΛ0 ω) (intensityStep_pos n)
  have hei (n : ℕ) : Integrable (fun ω => Real.exp (-(t n * Λ ω))) P := by
    refine Integrable.of_bound (hem n).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (intensityStep_pos n).le (hΛ0 ω)
  have hfi (n : ℕ) : Integrable (f n) P :=
    (((hei n).sub (integrable_const 1)).add (hΛi.const_mul (t n))).div_const _
  have hcn (n : ℕ) : ∫ ω, f n ω ∂P =
      (∫ ω, Real.exp (-(t n * Λ ω)) ∂P - 1 + t n * ∫ ω, Λ ω ∂P) / t n ^ 2 := by
    simp only [hf]
    rw [integral_div, integral_add (f := fun ω => Real.exp (-(t n * Λ ω)) - 1)
      (g := fun ω => t n * Λ ω) ((hei n).sub (integrable_const 1)) (hΛi.const_mul _),
      integral_sub (hei n) (integrable_const 1), integral_const, integral_const_mul]
    simp
  have hcn' (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P = ENNReal.ofReal
      ((∫ ω, Real.exp (-(t n * Λ ω)) ∂P - 1 + t n * ∫ ω, Λ ω ∂P) / t n ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall fun ω => (hfmem n ω).1), hcn]
  have hcE := (ENNReal.continuous_ofReal.tendsto _).comp hH
  apply le_antisymm
  · calc ∫⁻ ω, ENNReal.ofReal (Λ ω ^ 2 / 2) ∂P
          = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P := by
          refine lintegral_congr fun ω => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_exp_neg_quot_two (hΛ0 ω))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
          lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (hfm n)
      _ = ENNReal.ofReal H := by
          simp_rw [hcn']
          exact hcE.liminf_eq
  · refine le_of_tendsto' hcE fun n => ?_
    simp only [Function.comp_apply]
    rw [← hcn']
    exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hfmem n ω).2

/-!
## Second-order expansion of the decorated sine Laplace functional
-/

variable {r : ℕ}

/-- **Second-order expansion of the decorated sine Laplace functional** (deterministic).
For a nonnegative `f ∈ C_c(ℝ × ℂ^r)`, with `a(x) = ∫ f(x, g) dγ(g)`, `γ = circularVectorLaw (Fin r)`,
Lebesgue measure in `x`, along `t_n = intensityStep n = 1/(n+1)`:
`(decoratedSineLaplace r (t_n f) - 1 + t_n ∫ a)/t_n² → (∫∫ f²)/2 + sinePairForm a a / 2`.
-/
theorem tendsto_decoratedSineLaplace_quot_two
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    Tendsto (fun n => (decoratedSineLaplace r (intensityStep n • f) - 1 +
        intensityStep n * ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r)) / intensityStep n ^ 2)
      atTop (𝓝 ((∫ x, ∫ g, f (x, g) ^ 2 ∂circularVectorLaw (Fin r)) / 2 +
        sinePairForm (fun x => ∫ g, f (x, g) ∂circularVectorLaw (Fin r))
          (fun x => ∫ g, f (x, g) ∂circularVectorLaw (Fin r)) / 2)) := by
  set γ := circularVectorLaw (Fin r) with hγ
  set t := intensityStep with ht
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfM (z : ℝ × (Fin r → ℂ)) : f z ≤ M := by
    have := hM z; rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this
  set K₁ : Set ℝ := Prod.fst '' tsupport f with hK₁
  have hK₁c : IsCompact K₁ := f.hasCompactSupport.isCompact.image continuous_fst
  have hK₁m : MeasurableSet K₁ := hK₁c.isClosed.measurableSet
  have hzero (x : ℝ) (hx : x ∉ K₁) (g : Fin r → ℂ) : f (x, g) = 0 := by
    by_contra hne
    exact hx ⟨(x, g), subset_tsupport _ hne, rfl⟩
  have hfx (x : ℝ) : Continuous fun g : Fin r → ℂ => f (x, g) :=
    f.continuous.comp (Continuous.prodMk_right x)
  have hfjm : Measurable (fun p : ℝ × (Fin r → ℂ) => f p) := f.continuous.measurable
  set ind : ℝ → ℝ := K₁.indicator fun _ => 1 with hind
  have hindi : Integrable ind :=
    IntegrableOn.integrable_indicator (integrableOn_const hK₁c.measure_lt_top.ne) hK₁m
  have hind0 (x : ℝ) : 0 ≤ ind x := by
    simp only [hind]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set a : ℝ → ℝ := fun x => ∫ g, f (x, g) ∂γ with ha
  have ham : Measurable a :=
    (hfjm.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  have ha0 (x : ℝ) : 0 ≤ a x := integral_nonneg fun g => hf _
  have hab (x : ℝ) : a x ≤ M * ind x := by
    by_cases hx : x ∈ K₁
    · simp only [hind, Set.indicator_of_mem hx, mul_one]
      calc a x ≤ ∫ _g, M ∂γ := integral_mono_of_nonneg (Eventually.of_forall fun g => hf _)
              (integrable_const M) (Eventually.of_forall fun g => hfM _)
        _ = M := by simp
    · simp only [hind, Set.indicator_of_notMem hx, ha, mul_zero]
      simp [hzero x hx]
  have hai : Integrable a :=
    (hindi.const_mul M).mono' ham.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]; exact hab x)
  set G : ℝ := ∫ x, a x with hG
  have hG0 : 0 ≤ G := integral_nonneg ha0
  -- the weights `φ_n`
  set φ : ℕ → ℝ → ℝ := fun n x => 1 - ∫ g, Real.exp (-(t n * f (x, g))) ∂γ with hφ
  have hexpi (n : ℕ) (x : ℝ) : Integrable (fun g => Real.exp (-(t n * f (x, g)))) γ := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun g => ?_)
    · exact (Real.continuous_exp.comp ((continuous_const.mul (hfx x)).neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (intensityStep_pos n).le (hf _)
  have hfxi (x : ℝ) : Integrable (fun g => f (x, g)) γ :=
    Integrable.of_bound (hfx x).aestronglyMeasurable M (Eventually.of_forall fun g => hM _)
  have hφeq (n : ℕ) (x : ℝ) : φ n x = ∫ g, (1 - Real.exp (-(t n * f (x, g)))) ∂γ := by
    simp only [hφ]
    rw [integral_sub (integrable_const 1) (hexpi n x), integral_const]
    simp
  have hφmem (n : ℕ) (x : ℝ) : 0 ≤ φ n x ∧ φ n x ≤ t n * a x := by
    rw [hφeq]
    have hm (g : Fin r → ℂ) := one_sub_exp_neg_mem (t n * f (x, g))
      (mul_nonneg (intensityStep_pos n).le (hf _))
    constructor
    · exact integral_nonneg fun g => (hm g).1
    · rw [ha, ← integral_const_mul]
      exact integral_mono ((integrable_const 1).sub (hexpi n x)) ((hfxi x).const_mul _)
        fun g => (hm g).2
  have hφm (n : ℕ) : Measurable (φ n) := by
    have hj : Measurable (fun p : ℝ × (Fin r → ℂ) => Real.exp (-(t n * f p))) :=
      Real.measurable_exp.comp ((hfjm.const_mul _).neg)
    exact measurable_const.sub (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  have hφi (n : ℕ) : Integrable (φ n) := by
    refine (hai.const_mul (t n)).mono' (hφm n).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφmem n x).1]
    exact (hφmem n x).2
  have hL (n : ℕ) : decoratedSineLaplace r (t n • f) =
      fredholmSeries sineKernel volume (φ n) := by
    rw [decoratedSineLaplace_eq_fredholmSeries]
    rfl
  -- `φ_n / t_n → a` pointwise
  have hφt (x : ℝ) : Tendsto (fun n => φ n x / t n) atTop (𝓝 (a x)) := by
    have heq : (fun n => φ n x / t n) =
        fun n => ∫ g, (1 - Real.exp (-(t n * f (x, g)))) / t n ∂γ := by
      funext n; rw [hφeq, integral_div]
    rw [heq]
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
      (integrable_const M) (fun n => Eventually.of_forall fun g => ?_)
      (Eventually.of_forall fun g => tendsto_one_sub_exp_div _ (hf _))
    · exact ((Continuous.div_const (continuous_const.sub (Real.continuous_exp.comp
        ((continuous_const.mul (hfx x)).neg))) _)).aestronglyMeasurable
    · have hm := one_sub_exp_div_mem (f (x, g)) (t n) (hf _) (intensityStep_pos n)
      rw [Real.norm_eq_abs, abs_of_nonneg hm.1]
      exact hm.2.trans (hfM _)
  -- the three pieces
  set Q : ℕ → ℝ × (Fin r → ℂ) → ℝ := fun n p =>
    (Real.exp (-(t n * f p)) - 1 + t n * f p) / t n ^ 2 with hQ
  have hQc (n : ℕ) : Continuous (Q n) :=
    (((Real.continuous_exp.comp ((continuous_const.mul f.continuous).neg)).sub
      continuous_const).add (continuous_const.mul f.continuous)).div_const _
  have hQmem (n : ℕ) (p : ℝ × (Fin r → ℂ)) := exp_neg_quot_two_mem (hf p) (intensityStep_pos n)
  set T1 : ℕ → ℝ := fun n => ∫ x, ∫ g, Q n (x, g) ∂γ with hT1
  set T2 : ℕ → ℝ := fun n =>
    sinePairForm (fun x => φ n x / t n) (fun x => φ n x / t n) / 2 with hT2
  set T3 : ℕ → ℝ := fun n => (fredholmSeries sineKernel volume (φ n) -
    (1 - (∫ x, φ n x) + fredholmIntegral sineKernel volume (φ n) 2 / 2)) / t n ^ 2 with hT3
  have hT1eq (n : ℕ) : T1 n = (t n * G - ∫ x, φ n x) / t n ^ 2 := by
    have hin (x : ℝ) : ∫ g, Q n (x, g) ∂γ = (t n * a x - φ n x) / t n ^ 2 := by
      simp only [hQ]
      rw [integral_div]
      congr 1
      rw [integral_add (f := fun g => Real.exp (-(t n * f (x, g))) - 1)
        (g := fun g => t n * f (x, g)) ((hexpi n x).sub (integrable_const 1))
        ((hfxi x).const_mul _), integral_sub (hexpi n x) (integrable_const 1),
        integral_const, integral_const_mul]
      simp only [hφ, ha]
      simp
      ring
    simp only [hT1]
    simp_rw [hin]
    rw [integral_div, integral_sub (hai.const_mul _) (hφi n), integral_const_mul]
  have hT2eq (n : ℕ) : T2 n = fredholmIntegral sineKernel volume (φ n) 2 / 2 / t n ^ 2 := by
    rw [fredholmIntegral_two_sineKernel]
    simp only [hT2, sinePairForm]
    have hint : ∫ p : ℝ × ℝ, (1 - sineKernel p.1 p.2 ^ 2) * (φ n p.1 / t n * (φ n p.2 / t n))
        ∂(volume.prod volume) = (∫ p : ℝ × ℝ, (1 - sineKernel p.1 p.2 ^ 2) *
          (φ n p.1 * φ n p.2) ∂(volume.prod volume)) / t n ^ 2 := by
      rw [← integral_div]
      congr 1
      funext p
      ring
    rw [hint]
    ring
  have hsplit (n : ℕ) : (fredholmSeries sineKernel volume (φ n) - 1 + t n * G) / t n ^ 2 =
      T1 n + T2 n + T3 n := by
    rw [hT1eq, hT2eq]
    simp only [hT3]
    have htn : 0 < t n := intensityStep_pos n
    field_simp
    ring
  -- `T3 → 0`
  have hT3b (n : ℕ) : |T3 n| ≤ t n * (G ^ 3 / 6 * Real.exp G) := by
    have h2 := abs_fredholmSeries_sub_sum_le abs_det_sineKernel_le_one (hφi n) 3
    rw [sum_range_three_fredholmTerm] at h2
    simp_rw [sineKernel_self, one_mul] at h2
    have htn : 0 < t n := intensityStep_pos n
    have htn1 : t n ≤ 1 := intensityStep_le_one n
    have hA : ∫ x, |φ n x| ≤ t n * G := by
      rw [hG, ← integral_const_mul]
      exact integral_mono (hφi n).abs (hai.const_mul _) fun x => by
        rw [abs_of_nonneg (hφmem n x).1]; exact (hφmem n x).2
    have hA0 : 0 ≤ ∫ x, |φ n x| := integral_nonneg fun _ => abs_nonneg _
    simp only [hT3]
    rw [abs_div, abs_of_pos (by positivity : 0 < t n ^ 2), div_le_iff₀ (by positivity)]
    refine h2.trans ?_
    have h1 : ∫ x, |φ n x| ≤ G := hA.trans (by nlinarith)
    have h3 : (∫ x, |φ n x|) ^ 3 ≤ (t n * G) ^ 3 := pow_le_pow_left₀ hA0 hA 3
    have h4 : Real.exp (∫ x, |φ n x|) ≤ Real.exp G := Real.exp_le_exp.2 h1
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6]
    calc _ ≤ (t n * G) ^ 3 / 6 * Real.exp G :=
          mul_le_mul (div_le_div_of_nonneg_right h3 (by norm_num)) h4 (Real.exp_pos _).le
            (by positivity)
      _ = _ := by ring
  have hT3t : Tendsto T3 atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => t n * (G ^ 3 / 6 * Real.exp G))
      (fun n => by rw [Real.norm_eq_abs]; exact hT3b n) ?_
    simpa using tendsto_intensityStep.mul_const (G ^ 3 / 6 * Real.exp G)
  -- `T2 → sinePairForm a a / 2`
  have hT2t : Tendsto T2 atTop (𝓝 (sinePairForm a a / 2)) := by
    refine Tendsto.div_const ?_ 2
    refine tendsto_integral_of_dominated_convergence (fun p => a p.1 * a p.2) (fun n => ?_)
      (integrable_mul_prod hai hai) (fun n => Eventually.of_forall fun p => ?_)
      (Eventually.of_forall fun p => ?_)
    · exact ((continuous_const.sub (continuous_sineKernel.pow 2)).measurable.mul
        ((((hφm n).div_const _).comp measurable_fst).mul
          (((hφm n).div_const _).comp measurable_snd))).aestronglyMeasurable
    · have htn : 0 < t n := intensityStep_pos n
      have hb (x : ℝ) : |φ n x / t n| ≤ a x := by
        rw [abs_of_nonneg (div_nonneg (hφmem n x).1 htn.le), div_le_iff₀ htn]
        linarith [(hφmem n x).2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |1 - sineKernel p.1 p.2 ^ 2| * (|φ n p.1 / t n| * |φ n p.2 / t n|)
          ≤ 1 * (a p.1 * a p.2) :=
            mul_le_mul (abs_one_sub_sineKernel_sq_le_one _ _)
              (mul_le_mul (hb _) (hb _) (abs_nonneg _) (ha0 _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
        _ = a p.1 * a p.2 := one_mul _
    · exact ((hφt p.1).mul (hφt p.2)).const_mul _
  -- `T1 → (∫∫ f²)/2`
  have hT1t : Tendsto T1 atTop (𝓝 ((∫ x, ∫ g, f (x, g) ^ 2 ∂γ) / 2)) := by
    have hlim : (∫ x, ∫ g, f (x, g) ^ 2 ∂γ) / 2 = ∫ x, ∫ g, f (x, g) ^ 2 / 2 ∂γ := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun x => (integral_div _ _).symm)
    rw [hlim]
    refine tendsto_integral_of_dominated_convergence (fun x => M ^ 2 / 2 * ind x)
      (fun n => ((hQc n).measurable.stronglyMeasurable.integral_prod_right'
        (ν := γ)).aestronglyMeasurable)
      (hindi.const_mul _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ K₁
      · simp only [hind, Set.indicator_of_mem hx, mul_one]
        refine (norm_integral_le_of_norm_le_const (C := M ^ 2 / 2)
          (Eventually.of_forall fun g => ?_)).trans (by simp)
        rw [Real.norm_eq_abs, abs_of_nonneg (hQmem n _).1]
        refine (hQmem n _).2.trans ?_
        have := pow_le_pow_left₀ (hf (x, g)) (hfM (x, g)) 2
        linarith
      · simp only [hind, Set.indicator_of_notMem hx, mul_zero]
        simp [hQ, hzero x hx]
    · refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2 / 2)
        (fun n => ((hQc n).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
        (integrable_const _) (fun n => Eventually.of_forall fun g => ?_)
        (Eventually.of_forall fun g => tendsto_exp_neg_quot_two (hf (x, g)))
      rw [Real.norm_eq_abs, abs_of_nonneg (hQmem n _).1]
      refine (hQmem n _).2.trans ?_
      have := pow_le_pow_left₀ (hf (x, g)) (hfM (x, g)) 2
      linarith
  simp_rw [hL, hsplit]
  simpa using (hT1t.add hT2t).add hT3t

/-- **Second moment of a decorated sine linear statistic** (the `k = 2` Fredholm term).
Law: `Ξ` is a decorated sine process on `(Ω, P)` (`IsDecoratedSineProcess`; marks
`γ = circularVectorLaw (Fin r)`).
For every nonnegative
`f ∈ C_c(ℝ × ℂ^r)`, with `a(x) = ∫ f(x, g) dγ(g)` (Lebesgue measure in `x`):
`∫⁻ ω, ofReal ((∫ f dΞ(ω))²) dP = ofReal (∫ x, ∫ g, f(x,g)² dγ dx + sinePairForm a a)`,
where `sinePairForm a a = ∫∫ (1 - sinc(π(x-y))²) a(x) a(y) dx dy`.
-/
theorem lintegral_sq_coordinate_of_decoratedSine {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∫⁻ ω, ENNReal.ofReal ((∫ p, f p ∂(Ξ ω).measure) ^ 2) ∂P =
      ENNReal.ofReal ((∫ x, ∫ g, f (x, g) ^ 2 ∂circularVectorLaw (Fin r)) +
        sinePairForm (fun x => ∫ g, f (x, g) ∂circularVectorLaw (Fin r))
          (fun x => ∫ g, f (x, g) ∂circularVectorLaw (Fin r))) := by
  have := h.prob
  obtain ⟨hi, hE⟩ := integral_coordinate_of_decoratedSine h f hf
  set Λ : Ω → ℝ := fun ω => ∫ p, f p ∂(Ξ ω).measure with hΛ
  have hΛm : Measurable Λ :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate f).measurable.comp
      h.measurable
  have hΛ0 (ω : Ω) : 0 ≤ Λ ω := integral_nonneg hf
  have hLap (n : ℕ) : ∫ ω, Real.exp (-(intensityStep n * Λ ω)) ∂P =
      decoratedSineLaplace r (intensityStep n • f) := by
    have h1 := h.laplace (intensityStep n • f) fun z => by
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (intensityStep_pos n).le (hf z)
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      at h1
    exact h1
  have key := lintegral_sq_half_eq_of_tendsto hΛm hΛ0 hi (by
    simp_rw [hLap, hE]
    exact tendsto_decoratedSineLaplace_quot_two f hf)
  have h2 (ω : Ω) : ENNReal.ofReal (Λ ω ^ 2) = 2 * ENNReal.ofReal (Λ ω ^ 2 / 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hm2 : Measurable fun ω => ENNReal.ofReal (Λ ω ^ 2 / 2) :=
    ENNReal.measurable_ofReal.comp ((hΛm.pow_const 2).div_const 2)
  refine (lintegral_congr fun ω => h2 ω).trans ?_
  rw [lintegral_const_mul _ hm2,
    key, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  ring_nf

end BlockBand.Critical.Herglotz
