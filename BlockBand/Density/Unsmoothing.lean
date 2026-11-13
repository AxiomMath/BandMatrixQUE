module

public import BlockBand.Density.Smooth
public import BlockBand.Counting.PoissonUnsmoothingAnalysis

/-!
# Lipschitz bound and Poisson unsmoothing of the mean density

Deterministic, for a finite measure `ν` and `v > 0` with `ρ = gaussConv ν v ≤ K` pointwise:

* `gaussConv_add_le`: `gaussConv ν (v+v) ≤ K` (Gaussian semigroup `N(y,v) ∗ N(0,v) = N(y,2v)`);
* `abs_gaussConv_sub_le`: `|ρ x - ρ y| ≤ (2K/√v)|x - y|` (from `|u|/v φ_v(u) ≤ (2/√v) φ_{2v}(u)`);
* `abs_sub_poissonSmoothTest_le`: for continuous `f` with `|f| ≤ K`, `L`-Lipschitz, and every
  `h > 0`: `|f x - (P_δ ∗ f)(x)| ≤ L h + 4Kδ/(πh)`.
For the physical mean density (`meanDensity`, `v = c/(NW)`, `K = K_b`, PSSS) this gives
`|ρ_{n,W}(e) - (P_η∗ρ_{n,W})(e)| ≤ 2K_b√(NW/c)·h + 4K_bη/(πh)` (`meanDensity_unsmoothing`),
the third bound of the smooth-density estimate in split form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory ProbabilityTheory Set Filter BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal Topology

theorem gaussianPDFReal_symm (a x : ℝ) (v : ℝ≥0) : gaussianPDFReal a v x = gaussianPDFReal x v a := by
  simp only [gaussianPDFReal_def]
  congr 3
  ring

/-- `(P ∗ N(0,v))(S) = ∫ N(a,v)(S) dP(a)`. -/
theorem conv_gaussianReal_apply (P : Measure ℝ) [SFinite P] (v : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) : (P ∗ gaussianReal 0 v) S = ∫⁻ a, gaussianReal a v S ∂P := by
  have hadd : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := measurable_fst.add measurable_snd
  change Measure.map (fun q : ℝ × ℝ => q.1 + q.2) (P.prod (gaussianReal 0 v)) S = _
  rw [Measure.map_apply hadd hS, Measure.prod_apply (hadd hS)]
  apply lintegral_congr
  intro a
  rw [← zero_add a, ← gaussianReal_map_add_const a, Measure.map_apply (measurable_add_const a) hS,
    zero_add]
  congr 1
  ext x
  simp [add_comm]

theorem measurable_gaussianReal_apply (v : ℝ≥0) (hv : v ≠ 0) (S : Set ℝ) (_hS : MeasurableSet S) :
    Measurable (fun a : ℝ => gaussianReal a v S) := by
  simp_rw [gaussianReal_apply _ hv S, gaussianPDF_def]
  have hm : Measurable (Function.uncurry fun a x : ℝ =>
      S.indicator (fun x => ENNReal.ofReal (gaussianPDFReal a v x)) x) := by
    apply Measurable.indicator _ (measurable_snd _hS)
    exact ENNReal.measurable_ofReal.comp
      ((continuous_gaussianPDFReal_uncurry v).measurable)
  have := hm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  simp only [Function.uncurry] at this
  convert this using 2 with a
  rw [lintegral_indicator _hS]

theorem lintegral_gaussianReal_volume (v : ℝ≥0) (hv : v ≠ 0) (S : Set ℝ) :
    ∫⁻ a, gaussianReal a v S = volume S := by
  simp_rw [gaussianReal_apply _ hv S, gaussianPDF_def]
  rw [lintegral_lintegral_swap]
  · have h1 : ∀ x, ∫⁻ a, ENNReal.ofReal (gaussianPDFReal a v x) = 1 := by
      intro x
      simp_rw [gaussianPDFReal_symm _ x]
      have := lintegral_gaussianPDF_eq_one x hv
      simpa [gaussianPDF_def] using this
    simp_rw [h1]
    simp
  · exact (ENNReal.measurable_ofReal.comp
      (continuous_gaussianPDFReal_uncurry v).measurable).aemeasurable

/-- **Gaussian semigroup bound.** If `gaussConv ν v ≤ K` everywhere then
`gaussConv ν (v+v) ≤ K` everywhere. -/
theorem gaussConv_add_le (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0} (hv : 0 < (v : ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hρ : ∀ a, gaussConv ν v a ≤ K) (e : ℝ) :
    gaussConv ν (v + v) e ≤ K := by
  have hv0 : v ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have hvv : v + v ≠ 0 := by
    intro h; have : ((v + v : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
    push_cast at this; linarith
  have hvv' : 0 < ((v + v : ℝ≥0) : ℝ) := by push_cast; linarith
  apply le_of_withDensity_le_smul_volume (contDiff_gaussConv ν hvv').continuous hK _ e
  refine Measure.le_iff.mpr fun S hS => ?_
  rw [← lintegral_gaussianReal_eq_withDensity ν hvv S hS, Measure.smul_apply, smul_eq_mul]
  have hsplit : ∀ y, gaussianReal y (v + v) S = ∫⁻ a, gaussianReal a v S ∂(gaussianReal y v) := by
    intro y
    rw [← conv_gaussianReal_apply _ v S hS, gaussianReal_conv_gaussianReal, add_zero]
  simp_rw [hsplit]
  have hmS := measurable_gaussianReal_apply v hv0 S hS
  have hden : ∀ y, ∫⁻ a, gaussianReal a v S ∂(gaussianReal y v) =
      ∫⁻ a, ENNReal.ofReal (gaussianPDFReal y v a) * gaussianReal a v S := by
    intro y
    rw [gaussianReal_of_var_ne_zero y hv0, lintegral_withDensity_eq_lintegral_mul _
      (measurable_gaussianPDF y v) hmS]
    rfl
  simp_rw [hden]
  rw [lintegral_lintegral_swap]
  · have hin : ∀ a, ∫⁻ y, ENNReal.ofReal (gaussianPDFReal y v a) * gaussianReal a v S ∂ν =
        ENNReal.ofReal (gaussConv ν v a) * gaussianReal a v S := by
      intro a
      rw [lintegral_mul_const (f := fun y => ENNReal.ofReal (gaussianPDFReal y v a)) _
        (ENNReal.measurable_ofReal.comp
        ((continuous_gaussianPDFReal_uncurry v).comp
          (continuous_id.prodMk continuous_const)).measurable)]
      congr 1
      unfold gaussConv
      rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal_param ν v a)
        (Eventually.of_forall fun y => gaussianPDFReal_nonneg _ _ _)]
    simp_rw [hin]
    calc ∫⁻ a, ENNReal.ofReal (gaussConv ν v a) * gaussianReal a v S
        ≤ ∫⁻ a, ENNReal.ofReal K * gaussianReal a v S :=
          lintegral_mono fun a => mul_le_mul' (ENNReal.ofReal_le_ofReal (hρ a)) le_rfl
      _ = ENNReal.ofReal K * volume S := by
          rw [lintegral_const_mul _ hmS, lintegral_gaussianReal_volume v hv0 S]
  · apply Measurable.aemeasurable
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp (continuous_gaussianPDFReal_uncurry v).measurable
    · exact hmS.comp measurable_snd

theorem hasDerivAt_gaussianPDFReal (y : ℝ) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (e : ℝ) :
    HasDerivAt (fun e => gaussianPDFReal y v e) (-(e - y) / v * gaussianPDFReal y v e) e := by
  simp only [gaussianPDFReal_def]
  have h1 : HasDerivAt (fun e : ℝ => -(e - y) ^ 2 / (2 * (v : ℝ))) (-(e - y) / v) e := by
    have h0 := (((hasDerivAt_id e).sub_const y).pow 2).neg.div_const (2 * (v : ℝ))
    refine h0.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
  have := (h1.exp).const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert this using 1
  ring

theorem abs_deriv_pdf_le (y : ℝ) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (e : ℝ) :
    |-(e - y) / v * gaussianPDFReal y v e| ≤ 2 / Real.sqrt v * gaussianPDFReal y (v + v) e := by
  simp only [gaussianPDFReal_def]
  set a := e - y
  have hv2 : ((v + v : ℝ≥0) : ℝ) = 2 * v := by push_cast; ring
  rw [hv2]
  have hsv := Real.sqrt_pos.mpr hv
  have hs2 : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity [Real.pi_pos])
  have hs4 : 0 < Real.sqrt (2 * Real.pi * (2 * v)) := Real.sqrt_pos.mpr (by positivity [Real.pi_pos])
  have hsplit : Real.exp (-a ^ 2 / (2 * v)) =
      Real.exp (-a ^ 2 / (2 * (2 * v))) * Real.exp (-a ^ 2 / (2 * (2 * v))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hA := abs_mul_exp_neg_sq_le (by positivity : (0 : ℝ) < 2 * v) a
  have hE1 : Real.exp (-a ^ 2 / (2 * (2 * v))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg a]) (by positivity)
  have hrel : Real.sqrt (2 * Real.pi * (2 * v)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * v) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have h2v : Real.sqrt (2 * v) = Real.sqrt 2 * Real.sqrt v := by
    rw [← Real.sqrt_mul (by norm_num)]
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqv : Real.sqrt (v : ℝ) * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hX : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-a ^ 2 / (2 * v)) := by positivity
  rw [abs_mul, abs_of_nonneg hX, abs_div, abs_neg, abs_of_pos hv, hsplit]
  -- |a| E E /(v s2) ≤ 2/√v · E/s4
  have key : |a| * Real.exp (-a ^ 2 / (2 * (2 * v))) ≤ Real.sqrt 2 * Real.sqrt v := by
    rw [← h2v]; convert hA using 2
  rw [hrel]
  have hE0 := Real.exp_pos (-a ^ 2 / (2 * (2 * v)))
  calc |a| / v * ((Real.sqrt (2 * Real.pi * v))⁻¹ *
        (Real.exp (-a ^ 2 / (2 * (2 * v))) * Real.exp (-a ^ 2 / (2 * (2 * v)))))
      = (|a| * Real.exp (-a ^ 2 / (2 * (2 * v)))) * Real.exp (-a ^ 2 / (2 * (2 * v))) /
          (v * Real.sqrt (2 * Real.pi * v)) := by field_simp
    _ ≤ (Real.sqrt 2 * Real.sqrt v) * Real.exp (-a ^ 2 / (2 * (2 * v))) /
          (v * Real.sqrt (2 * Real.pi * v)) := by gcongr
    _ = 2 / Real.sqrt v * ((Real.sqrt 2 * Real.sqrt (2 * Real.pi * v))⁻¹ *
          Real.exp (-a ^ 2 / (2 * (2 * v)))) := by
        field_simp
        nlinarith [hsq2, hsqv]

/-- Derivative of the Gaussian convolution. -/
theorem hasDerivAt_gaussConv (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0} (hv : 0 < (v : ℝ))
    (e : ℝ) : HasDerivAt (gaussConv ν v)
      (∫ y, -(e - y) / v * gaussianPDFReal y v e ∂ν) e := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ)
    (F := fun e y => gaussianPDFReal y v e)
    (F' := fun e y => -(e - y) / v * gaussianPDFReal y v e)
    (bound := fun _ => 2 / Real.sqrt v * (Real.sqrt (2 * Real.pi * (v + v : ℝ≥0)))⁻¹)
    (x₀ := e) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x => ((continuous_gaussianPDFReal_uncurry v).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_gaussianPDFReal_param ν v e)
    (by
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul (by fun_prop)
      exact (continuous_gaussianPDFReal_uncurry v).comp (continuous_id.prodMk continuous_const))
    (Eventually.of_forall fun y x _ => by
      rw [Real.norm_eq_abs]
      refine (abs_deriv_pdf_le y hv x).trans ?_
      exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le _ _ _) (by positivity))
    (integrable_const _)
    (Eventually.of_forall fun y x _ => hasDerivAt_gaussianPDFReal y hv x)
  exact hd.2

/-- **Lipschitz bound** (second bound of the smooth-density estimate). -/
theorem abs_gaussConv_sub_le (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0} (hv : 0 < (v : ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hρ : ∀ a, gaussConv ν v a ≤ K) (x y : ℝ) :
    |gaussConv ν v x - gaussConv ν v y| ≤ 2 * K / Real.sqrt v * |x - y| := by
  have hder : ∀ e, ‖deriv (gaussConv ν v) e‖ ≤ 2 * K / Real.sqrt v := by
    intro e
    rw [(hasDerivAt_gaussConv ν hv e).deriv, Real.norm_eq_abs]
    calc |∫ y, -(e - y) / v * gaussianPDFReal y v e ∂ν|
        ≤ ∫ y, 2 / Real.sqrt v * gaussianPDFReal y (v + v) e ∂ν := by
          rw [← Real.norm_eq_abs]
          apply norm_integral_le_of_norm_le
            ((integrable_gaussianPDFReal_param ν (v + v) e).const_mul _)
          exact Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]; exact abs_deriv_pdf_le y hv e
      _ = 2 / Real.sqrt v * gaussConv ν (v + v) e := by
          rw [integral_const_mul]; rfl
      _ ≤ 2 / Real.sqrt v * K :=
          mul_le_mul_of_nonneg_left (gaussConv_add_le ν hv hK hρ e) (by positivity)
      _ = 2 * K / Real.sqrt v := by ring
  have hdiff : ∀ e, DifferentiableAt ℝ (gaussConv ν v) e := fun e =>
    (hasDerivAt_gaussConv ν hv e).differentiableAt
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun e _ => hdiff e) (fun e _ => hder e)
    (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- **Poisson unsmoothing** of a bounded Lipschitz function, at any split scale `h > 0`. -/
theorem abs_sub_poissonSmoothTest_le (f : ℝ → ℝ) (hf : Continuous f) {K L δ h : ℝ}
    (hK : ∀ x, |f x| ≤ K) (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (hL0 : 0 ≤ L) (hδ : 0 < δ)
    (hh : 0 < h) (x : ℝ) :
    |f x - poissonSmoothTest δ f x| ≤ L * h + 2 * K * (2 * δ / (Real.pi * h)) := by
  rw [poisson_unsmoothing_difference_eq_integral f hf K δ hδ hK x]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hm : MeasurableSet {t : ℝ | h < |t|} := measurableSet_lt measurable_const measurable_abs
  set bound : ℝ → ℝ := fun t => L * h * Counting.poissonKernel δ t +
    2 * K * ({t : ℝ | h < |t|}.indicator (Counting.poissonKernel δ) t)
  have hbi : Integrable bound :=
    ((integrable_poissonKernel hδ).const_mul _).add
      (((integrable_poissonKernel hδ).indicator hm).const_mul _)
  have hpt : ∀ t, ‖Counting.poissonKernel δ t * (f x - f (x + t))‖ ≤ bound t := by
    intro t
    have hP := poissonKernel_nonneg hδ t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
    by_cases ht : h < |t|
    · simp only [bound, indicator_of_mem (show t ∈ {t : ℝ | h < |t|} from ht)]
      have : |f x - f (x + t)| ≤ 2 * K := by
        have := abs_sub (f x) (f (x + t))
        linarith [hK x, hK (x + t)]
      nlinarith [mul_nonneg (mul_nonneg hL0 hh.le) hP]
    · simp only [bound, indicator_of_notMem (show t ∉ {t : ℝ | h < |t|} from ht), mul_zero,
        add_zero]
      have h1 : |f x - f (x + t)| ≤ L * h := by
        refine (hL x (x + t)).trans ?_
        rw [show x - (x + t) = -t by ring, abs_neg]
        exact mul_le_mul_of_nonneg_left (not_lt.mp ht) hL0
      nlinarith
  refine (norm_integral_le_of_norm_le hbi (Eventually.of_forall hpt)).trans ?_
  simp only [bound]
  rw [integral_add ((integrable_poissonKernel hδ).const_mul _)
    (((integrable_poissonKernel hδ).indicator hm).const_mul _), integral_const_mul,
    integral_const_mul, integral_poissonKernel hδ, integral_indicator hm, mul_one]
  have := integral_poissonKernel_tail_le hδ hh
  nlinarith

/-- The physical unsmoothing bound: for every admissible `p`, realization, `η > 0`, `h > 0`,
`|ρ_{n,W}(e) - (P_η∗ρ_{n,W})(e)| ≤ 2K_b/√(c/(NW))·h + 4K_bη/(πh)`. Uses `PSSS.SourceContract`. -/
theorem meanDensity_unsmoothing (source : PSSS.SourceContract.{0}) (p : Parameters)
    (model : p.GaussianRingModel) {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (e : ℝ) :
    |meanDensity p model e - poissonSmoothTest η (meanDensity p model) e| ≤
      2 * densityBound source p.b / Real.sqrt (p.scalarTraceVariance : ℝ) * h +
        2 * densityBound source p.b * (2 * η / (Real.pi * h)) := by
  have hK := (densityBound_pos source p.b_lt_half).le
  have hle := meanDensity_le source p model
  apply abs_sub_poissonSmoothTest_le _ (contDiff_meanDensity p model).continuous
    (fun x => by rw [abs_of_pos (meanDensity_pos p model x)]; exact hle x)
    (abs_gaussConv_sub_le _ (scalarTraceVariance_pos p) hK hle) (by positivity) hη hh e

end BlockBand.Density
