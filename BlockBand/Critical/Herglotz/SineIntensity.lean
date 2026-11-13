module

public import BlockBand.Critical.Herglotz.Canonical
public import BlockBand.Endpoints.Sine.Intensity
public import BlockBand.Endpoints.Sine.Law
public import BlockBand.Coarea.ProjectiveHaar

/-!
# Intensity of the decorated sine process

The Herglotz tail lemma and the moments of the canonical Cauchy series use the first intensity
of the unit-intensity sine process with independent standard circular Gaussian decorations:
`E Σ_j f(x_j, g_j) = ∫∫ f(x, g) dγ(g) dx`.

This is derived from the definition `IsDecoratedSineProcess` (Laplace functional
`decoratedSineLaplace`) only. It reuses the sine-law toolkit of `BlockBand.Endpoints`: the step
`intensityStep n = 1/(n+1)` and its elementary bounds, the first-order Fredholm expansion
`abs_fredholmSeries_sub_first_le`, the determinant bound `abs_det_sineKernel_le_one`, and
`sineKernel_self`. The proof is the one of `lintegral_coordinate_eq_of_fredholm`, with the weight
`φ_t(x) = 1 - ∫ e^{-t f(x,g)} dγ(g)` in place of `1 - e^{-t f(x)}`.

* `lintegral_ofReal_eq_of_tendsto_laplaceQuotient` — abstract step: for `Λ ≥ 0` measurable,
  if `(1 - E e^{-t_n Λ})/t_n → G`, then `E Λ = G` (lintegral form).
* `decoratedSineLaplace_eq_fredholmSeries` — the decorated Laplace functional is
  `fredholmSeries sineKernel volume φ` (definitional).
* `lintegral_coordinate_of_decoratedSine` — **intensity**: for nonnegative
  `f ∈ C_c(ℝ × ℂ^r)`, `∫⁻ ofReal (∫ f dΞ) dP = ofReal (∫ x, ∫ g, f(x,g) dγ dx)`.
* `integral_coordinate_of_decoratedSine` — the same with integrability, Bochner form.
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
  fredholmSeries abs_fredholmSeries_sub_first_le abs_det_sineKernel_le_one sineKernel_self)

/-- **Intensity from Laplace difference quotients.** For a nonnegative measurable `Λ` on a
probability space, if `(1 - E e^{-t_n Λ})/t_n → G` along `t_n = 1/(n+1)`, then
`∫⁻ ofReal Λ = ofReal G`. -/
theorem lintegral_ofReal_eq_of_tendsto_laplaceQuotient {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ0 : ∀ ω, 0 ≤ Λ ω) {G : ℝ}
    (hG : Tendsto (fun n => (1 - ∫ ω, Real.exp (-(intensityStep n * Λ ω)) ∂P) /
      intensityStep n) atTop (𝓝 G)) :
    ∫⁻ ω, ENNReal.ofReal (Λ ω) ∂P = ENNReal.ofReal G := by
  set t := intensityStep with ht
  set f : ℕ → Ω → ℝ := fun n ω => (1 - Real.exp (-(t n * Λ ω))) / t n with hf
  have hfm (n : ℕ) : Measurable (f n) := by
    refine Measurable.div_const (measurable_const.sub ?_) _
    exact Real.measurable_exp.comp ((hΛm.const_mul _).neg)
  have hfmem (n : ℕ) (ω : Ω) := one_sub_exp_div_mem (Λ ω) (t n) (hΛ0 ω) (intensityStep_pos n)
  have hei (n : ℕ) : Integrable (fun ω => Real.exp (-(t n * Λ ω))) P := by
    refine Integrable.of_bound (Real.measurable_exp.comp
      ((hΛm.const_mul _).neg)).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (intensityStep_pos n).le (hΛ0 ω)
  have hfi (n : ℕ) : Integrable (f n) P :=
    ((integrable_const 1).sub (hei n)).div_const _
  set c : ℕ → ℝ := fun n => (1 - ∫ ω, Real.exp (-(t n * Λ ω)) ∂P) / t n with hc
  have hcn (n : ℕ) : ∫ ω, f n ω ∂P = c n := by
    simp only [hf, hc]
    rw [integral_div, integral_sub (integrable_const 1) (hei n), integral_const]
    simp
  have hcn' (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P = ENNReal.ofReal (c n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall fun ω => (hfmem n ω).1), hcn]
  have hcE : Tendsto (fun n => ENNReal.ofReal (c n)) atTop (𝓝 (ENNReal.ofReal G)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hG
  apply le_antisymm
  · calc ∫⁻ ω, ENNReal.ofReal (Λ ω) ∂P
          = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P := by
          refine lintegral_congr fun ω => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_one_sub_exp_div (Λ ω) (hΛ0 ω))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
          lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (hfm n)
      _ = ENNReal.ofReal G := by
          simp_rw [hcn']
          exact hcE.liminf_eq
  · refine le_of_tendsto' hcE fun n => ?_
    rw [← hcn']
    exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hfmem n ω).2

/-- The decorated sine Laplace functional is the Fredholm series with kernel
`sineKernel`, Lebesgue reference measure and weight `x ↦ 1 - ∫ e^{-f(x,g)} dγ(g)`. -/
theorem decoratedSineLaplace_eq_fredholmSeries (r : ℕ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) :
    decoratedSineLaplace r f = fredholmSeries sineKernel volume
      (fun x => 1 - ∫ g, Real.exp (-f (x, g)) ∂circularVectorLaw (Fin r)) := rfl

variable {r : ℕ}

/-- **Intensity of the decorated sine process** (lintegral form). Law: `Ξ` is a decorated sine
process on `(Ω, P)` (`IsDecoratedSineProcess`: unit-intensity sine process with
independent standard circular Gaussian marks `γ = circularVectorLaw (Fin r)`). For every
nonnegative `f ∈ C_c(ℝ × ℂ^r)`:
`∫⁻ ω, ofReal (∫ f dΞ(ω)) dP = ofReal (∫ x, ∫ g, f(x,g) dγ(g) dx)`. -/
theorem lintegral_coordinate_of_decoratedSine {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∫⁻ ω, ENNReal.ofReal (∫ p, f p ∂(Ξ ω).measure) ∂P =
      ENNReal.ofReal (∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r)) := by
  have := h.prob
  set γ := circularVectorLaw (Fin r) with hγ
  set t := intensityStep with ht
  set Λ : Ω → ℝ := fun ω => ∫ p, f p ∂(Ξ ω).measure with hΛ
  have hΛm : Measurable Λ :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate f).measurable.comp
      h.measurable
  have hΛ0 (ω : Ω) : 0 ≤ Λ ω := integral_nonneg hf
  -- deterministic data: bound, support, the mark average `a`
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
  set b : ℝ → ℝ := K₁.indicator fun _ => M with hb
  have hbi : Integrable b := by
    refine IntegrableOn.integrable_indicator ?_ hK₁m
    exact integrableOn_const hK₁c.measure_lt_top.ne
  have hfjm : Measurable (fun p : ℝ × (Fin r → ℂ) => f p) := f.continuous.measurable
  set a : ℝ → ℝ := fun x => ∫ g, f (x, g) ∂γ with ha
  have ham : Measurable a :=
    (hfjm.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  have ha0 (x : ℝ) : 0 ≤ a x := integral_nonneg fun g => hf _
  have hab (x : ℝ) : a x ≤ b x := by
    by_cases hx : x ∈ K₁
    · simp only [hb, Set.indicator_of_mem hx]
      calc a x ≤ ∫ _g, M ∂γ := integral_mono_of_nonneg (Eventually.of_forall fun g => hf _)
              (integrable_const M) (Eventually.of_forall fun g => hfM _)
        _ = M := by simp
    · simp only [hb, Set.indicator_of_notMem hx, ha]
      simp [hzero x hx]
  have hai : Integrable a :=
    hbi.mono' ham.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]; exact hab x)
  set G : ℝ := ∫ x, a x with hG
  have hG0 : 0 ≤ G := integral_nonneg ha0
  -- the weights `φ_n`
  set φ : ℕ → ℝ → ℝ := fun n x => 1 - ∫ g, Real.exp (-(t n * f (x, g))) ∂γ with hφ
  have hexpi (n : ℕ) (x : ℝ) : Integrable (fun g => Real.exp (-(t n * f (x, g)))) γ := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun g => ?_)
    · exact (Real.continuous_exp.comp ((continuous_const.mul (f.continuous.comp
        (Continuous.prodMk_right x))).neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (intensityStep_pos n).le (hf _)
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
      refine integral_mono ((integrable_const 1).sub (hexpi n x)) ?_ fun g => (hm g).2
      exact (Integrable.of_bound (f.continuous.comp
        (Continuous.prodMk_right x)).aestronglyMeasurable M
        (Eventually.of_forall fun g => hM _)).const_mul _
  have hφm (n : ℕ) : Measurable (φ n) := by
    have hj : Measurable (fun p : ℝ × (Fin r → ℂ) => Real.exp (-(t n * f p))) :=
      Real.measurable_exp.comp ((hfjm.const_mul _).neg)
    exact measurable_const.sub (hj.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  have hφi (n : ℕ) : Integrable (φ n) := by
    refine (hai.const_mul (t n)).mono' (hφm n).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφmem n x).1]
    exact (hφmem n x).2
  -- the Laplace functional at `t_n f`
  have hL (n : ℕ) : ∫ ω, Real.exp (-(t n * Λ ω)) ∂P = fredholmSeries sineKernel volume (φ n) := by
    have h1 := h.laplace (t n • f) fun z => by
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (intensityStep_pos n).le (hf z)
    rw [decoratedSineLaplace_eq_fredholmSeries] at h1
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      at h1
    exact h1
  -- the difference quotients
  apply lintegral_ofReal_eq_of_tendsto_laplaceQuotient hΛm hΛ0
  show Tendsto (fun n => (1 - ∫ ω, Real.exp (-(t n * Λ ω)) ∂P) / t n) atTop (𝓝 G)
  simp_rw [hL]
  have hmain : Tendsto (fun n => ∫ x, φ n x / t n) atTop (𝓝 G) := by
    refine tendsto_integral_of_dominated_convergence a (fun n => ((hφi n).div_const _).aestronglyMeasurable)
      hai (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have htn := intensityStep_pos n
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hφmem n x).1 htn.le), div_le_iff₀ htn]
      linarith [(hφmem n x).2]
    · -- dominated convergence in the mark
      have heq : (fun n => φ n x / t n) =
          fun n => ∫ g, (1 - Real.exp (-(t n * f (x, g)))) / t n ∂γ := by
        funext n; rw [hφeq, integral_div]
      rw [heq]
      refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
        (integrable_const M) (fun n => Eventually.of_forall fun g => ?_)
        (Eventually.of_forall fun g => tendsto_one_sub_exp_div _ (hf _))
      · exact ((Continuous.div_const (continuous_const.sub (Real.continuous_exp.comp
          ((continuous_const.mul (f.continuous.comp
          (Continuous.prodMk_right x))).neg))) _)).aestronglyMeasurable
      · have hm := one_sub_exp_div_mem (f (x, g)) (t n) (hf _) (intensityStep_pos n)
        rw [Real.norm_eq_abs, abs_of_nonneg hm.1]
        exact hm.2.trans (hfM _)
  have hA (n : ℕ) : ∫ x, |φ n x| ≤ t n * G := by
    rw [hG, ← integral_const_mul]
    exact integral_mono (hφi n).abs (hai.const_mul _) fun x => by
      rw [abs_of_nonneg (hφmem n x).1]; exact (hφmem n x).2
  have hA0 (n : ℕ) : 0 ≤ ∫ x, |φ n x| := integral_nonneg fun _ => abs_nonneg _
  have hR (n : ℕ) : |(fredholmSeries sineKernel volume (φ n) - (1 - ∫ x, φ n x)) / t n| ≤
      t n * (G ^ 2 / 2 * Real.exp G) := by
    have h2 := abs_fredholmSeries_sub_first_le abs_det_sineKernel_le_one (hφi n)
    simp_rw [sineKernel_self, one_mul] at h2
    have htn := intensityStep_pos n
    have htn1 := intensityStep_le_one n
    rw [abs_div, abs_of_pos htn, div_le_iff₀ htn]
    refine h2.trans ?_
    have h1 : ∫ x, |φ n x| ≤ G := (hA n).trans (by nlinarith)
    have h3 : (∫ x, |φ n x|) ^ 2 ≤ (t n * G) ^ 2 := pow_le_pow_left₀ (hA0 n) (hA n) 2
    have h4 : Real.exp (∫ x, |φ n x|) ≤ Real.exp G := Real.exp_le_exp.2 h1
    calc _ ≤ (t n * G) ^ 2 / 2 * Real.exp G :=
          mul_le_mul (div_le_div_of_nonneg_right h3 two_pos.le) h4 (Real.exp_pos _).le
            (by positivity)
      _ = _ := by ring
  have hRt : Tendsto (fun n => (fredholmSeries sineKernel volume (φ n) - (1 - ∫ x, φ n x)) / t n)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => t n * (G ^ 2 / 2 * Real.exp G))
      (fun n => by rw [Real.norm_eq_abs]; exact hR n) ?_
    simpa using tendsto_intensityStep.mul_const (G ^ 2 / 2 * Real.exp G)
  have heq : (fun n => (1 - fredholmSeries sineKernel volume (φ n)) / t n) = fun n =>
      (∫ x, φ n x / t n) - (fredholmSeries sineKernel volume (φ n) - (1 - ∫ x, φ n x)) / t n := by
    funext n
    have hd : (∫ x, φ n x / t n) = (∫ x, φ n x) / t n := integral_div (t n) (φ n)
    rw [hd]
    ring
  rw [heq]
  simpa using hmain.sub hRt

/-- **Intensity of the decorated sine process** (Bochner form): for nonnegative
`f ∈ C_c(ℝ × ℂ^r)`, `ω ↦ ∫ f dΞ(ω)` is integrable and `E ∫ f dΞ = ∫ x, ∫ g, f(x,g) dγ dx`. -/
theorem integral_coordinate_of_decoratedSine {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    Integrable (fun ω => ∫ p, f p ∂(Ξ ω).measure) P ∧
      ∫ ω, (∫ p, f p ∂(Ξ ω).measure) ∂P =
        ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) := by
  have hL := lintegral_coordinate_of_decoratedSine h f hf
  have hm : Measurable (fun ω => ∫ p, f p ∂(Ξ ω).measure) :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate f).measurable.comp
      h.measurable
  have h0 : 0 ≤ᵐ[P] (fun ω => ∫ p, f p ∂(Ξ ω).measure) :=
    Eventually.of_forall fun ω => integral_nonneg hf
  have hG0 : 0 ≤ ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) :=
    integral_nonneg fun x => integral_nonneg fun g => hf _
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 ?_⟩, ?_⟩
  · rw [hL]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae h0 hm.aestronglyMeasurable, hL,
      ENNReal.toReal_ofReal hG0]

end BlockBand.Critical.Herglotz
