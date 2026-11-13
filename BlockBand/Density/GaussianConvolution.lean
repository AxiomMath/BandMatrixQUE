module

public import Mathlib

/-!
# Gaussian convolution of a finite measure: smooth, strictly positive density

For every finite measure `ν` on `ℝ` and every variance `v > 0`, the function
`gaussConv ν v e = ∫ φ_{y,v}(e) dν(y)` (`φ` = `gaussianPDFReal`) is `C^∞` (it is the restriction of
the entire function `z ↦ ∫ exp(-(z-y)²/(2v)) dν(y)`, whose complex differentiability follows from
dominated parametric differentiation), it is strictly positive when `ν ≠ 0`, and it is the
Lebesgue density of `S ↦ ∫ N(y,v)(S) dν(y)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ContDiff

/-- `|a| exp(-a²/(2v)) ≤ √v`. -/
theorem abs_mul_exp_neg_sq_le {v : ℝ} (hv : 0 < v) (a : ℝ) :
    |a| * Real.exp (-a ^ 2 / (2 * v)) ≤ Real.sqrt v := by
  have hs := Real.sqrt_pos.mpr hv
  have hss : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  have h1 := Real.add_one_le_exp (a ^ 2 / (2 * v))
  have h2 : |a| ≤ Real.sqrt v * (a ^ 2 / (2 * v) + 1) := by
    have ha : |a| ^ 2 = a ^ 2 := sq_abs a
    rw [div_add_one (by positivity), mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|a| - Real.sqrt v), abs_nonneg a]
  have h3 : |a| ≤ Real.sqrt v * Real.exp (a ^ 2 / (2 * v)) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hs.le)
  have he : Real.exp (-a ^ 2 / (2 * v)) * Real.exp (a ^ 2 / (2 * v)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc |a| * Real.exp (-a ^ 2 / (2 * v))
      ≤ Real.sqrt v * Real.exp (a ^ 2 / (2 * v)) * Real.exp (-a ^ 2 / (2 * v)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.sqrt v := by rw [mul_assoc, mul_comm (Real.exp _), he, mul_one]

/-- The complex Gaussian kernel `exp(-(z-y)²/(2v))`. -/
def gaussKernelC (v : ℝ) (z : ℂ) (y : ℝ) : ℂ := Complex.exp (-(z - y) ^ 2 / (2 * v))

/-- Its `z`-derivative. -/
def gaussKernelC' (v : ℝ) (z : ℂ) (y : ℝ) : ℂ := -(z - y) / v * gaussKernelC v z y

theorem hasDerivAt_gaussKernelC {v : ℝ} (hv : 0 < v) (z : ℂ) (y : ℝ) :
    HasDerivAt (fun w => gaussKernelC v w y) (gaussKernelC' v z y) z := by
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have h : HasDerivAt (fun w : ℂ => -(w - y) ^ 2 / (2 * v)) (-(z - y) / v) z := by
    have h0 := ((hasDerivAt_id z).sub_const (y : ℂ)).pow 2
    have h1 := (h0.neg).div_const (2 * (v : ℂ))
    refine h1.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
  have := h.cexp
  unfold gaussKernelC' gaussKernelC
  convert this using 1
  ring

theorem norm_gaussKernelC (v : ℝ) (z : ℂ) (y : ℝ) :
    ‖gaussKernelC v z y‖ = Real.exp (-((z.re - y) ^ 2 - z.im ^ 2) / (2 * v)) := by
  unfold gaussKernelC
  rw [Complex.norm_exp]
  congr 1
  have h2 : (2 * (v : ℂ)) = ((2 * v : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.div_ofReal_re]
  simp [sq, Complex.mul_re]

theorem norm_gaussKernelC_le {v : ℝ} (hv : 0 < v) (z : ℂ) (y : ℝ) :
    ‖gaussKernelC v z y‖ ≤ Real.exp (z.im ^ 2 / (2 * v)) := by
  rw [norm_gaussKernelC]
  apply Real.exp_le_exp.mpr
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [sq_nonneg (z.re - y)]

theorem norm_gaussKernelC'_le {v : ℝ} (hv : 0 < v) (z : ℂ) (y : ℝ) {R : ℝ} (hR : |z.im| ≤ R) :
    ‖gaussKernelC' v z y‖ ≤ (Real.sqrt v + R) / v * Real.exp (R ^ 2 / (2 * v)) := by
  unfold gaussKernelC'
  rw [norm_mul, norm_div, norm_neg, norm_gaussKernelC]
  have hvn : ‖(v : ℂ)‖ = v := by simp [abs_of_pos hv]
  rw [hvn]
  set a := z.re - y
  set b := z.im
  have hzy : ‖z - (y : ℂ)‖ ≤ |a| + |b| := by
    have : z - (y : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [a, b]
    rw [this]
    refine (norm_add_le _ _).trans ?_
    simp
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hb2 : b ^ 2 ≤ R ^ 2 := by
    have := sq_abs b
    nlinarith [abs_nonneg b]
  have hsplit : Real.exp (-(a ^ 2 - b ^ 2) / (2 * v)) =
      Real.exp (-a ^ 2 / (2 * v)) * Real.exp (b ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hE : Real.exp (b ^ 2 / (2 * v)) ≤ Real.exp (R ^ 2 / (2 * v)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hb2 (by positivity))
  have hA := abs_mul_exp_neg_sq_le hv a
  have hA1 : Real.exp (-a ^ 2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg a]) (by positivity)
  have hb : |b| ≤ R := hR
  have key : ‖z - (y : ℂ)‖ * Real.exp (-a ^ 2 / (2 * v)) ≤ Real.sqrt v + R := by
    calc ‖z - (y : ℂ)‖ * Real.exp (-a ^ 2 / (2 * v))
        ≤ (|a| + |b|) * Real.exp (-a ^ 2 / (2 * v)) :=
          mul_le_mul_of_nonneg_right hzy (Real.exp_pos _).le
      _ = |a| * Real.exp (-a ^ 2 / (2 * v)) + |b| * Real.exp (-a ^ 2 / (2 * v)) := by ring
      _ ≤ Real.sqrt v + R * 1 := by
          gcongr
      _ = Real.sqrt v + R := by ring
  calc ‖z - (y : ℂ)‖ / v * (Real.exp (-a ^ 2 / (2 * v)) * Real.exp (b ^ 2 / (2 * v)))
      = (‖z - (y : ℂ)‖ * Real.exp (-a ^ 2 / (2 * v))) / v * Real.exp (b ^ 2 / (2 * v)) := by
        ring
    _ ≤ (Real.sqrt v + R) / v * Real.exp (R ^ 2 / (2 * v)) := by
        gcongr

theorem continuous_gaussKernelC (v : ℝ) (z : ℂ) : Continuous (gaussKernelC v z) := by
  unfold gaussKernelC
  fun_prop

theorem continuous_gaussKernelC' (v : ℝ) (z : ℂ) : Continuous (gaussKernelC' v z) := by
  unfold gaussKernelC' gaussKernelC
  fun_prop

/-- The entire extension `z ↦ ∫ exp(-(z-y)²/(2v)) dν(y)`. -/
def gaussConvC (ν : Measure ℝ) (v : ℝ) (z : ℂ) : ℂ := ∫ y, gaussKernelC v z y ∂ν

theorem integrable_gaussKernelC (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ} (hv : 0 < v)
    (z : ℂ) : Integrable (gaussKernelC v z) ν :=
  (integrable_const (Real.exp (z.im ^ 2 / (2 * v)))).mono'
    (continuous_gaussKernelC v z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => norm_gaussKernelC_le hv z y)

theorem differentiable_gaussConvC (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ} (hv : 0 < v) :
    Differentiable ℂ (gaussConvC ν v) := by
  intro z₀
  set R := |z₀.im| + 1
  have hball : Metric.ball z₀ 1 ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℂ)
    (F := fun z y => gaussKernelC v z y) (F' := fun z y => gaussKernelC' v z y)
    (bound := fun _ => (Real.sqrt v + R) / v * Real.exp (R ^ 2 / (2 * v))) hball
    (Filter.Eventually.of_forall fun z => (continuous_gaussKernelC v z).aestronglyMeasurable)
    (integrable_gaussKernelC ν hv z₀)
    (continuous_gaussKernelC' v z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y z hz => by
      apply norm_gaussKernelC'_le hv z y
      have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h3 : |z.im| ≤ |z.im - z₀.im| + |z₀.im| := by
        have := abs_add_le (z.im - z₀.im) z₀.im
        simpa using this
      change |z.im| ≤ |z₀.im| + 1
      linarith)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y z _ => hasDerivAt_gaussKernelC hv z y)
  exact hd.2.differentiableAt

/-- The Gaussian convolution density `e ↦ ∫ φ_{y,v}(e) dν(y)`. -/
def gaussConv (ν : Measure ℝ) (v : ℝ≥0) (e : ℝ) : ℝ := ∫ y, gaussianPDFReal y v e ∂ν

theorem gaussianPDFReal_eq_kernel (v : ℝ≥0) (y e : ℝ) :
    gaussianPDFReal y v e =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * (gaussKernelC v (e : ℂ) y).re := by
  rw [gaussianPDFReal_def]
  unfold gaussKernelC
  have : -((e : ℂ) - y) ^ 2 / (2 * (v : ℝ)) = ((-(e - y) ^ 2 / (2 * (v : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, ← Complex.ofReal_exp, Complex.ofReal_re]

theorem gaussConv_eq_re (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0} (hv : 0 < (v : ℝ))
    (e : ℝ) :
    gaussConv ν v e = (Real.sqrt (2 * Real.pi * v))⁻¹ * (gaussConvC ν v (e : ℂ)).re := by
  unfold gaussConv gaussConvC
  simp_rw [gaussianPDFReal_eq_kernel]
  rw [integral_const_mul]
  congr 1
  exact integral_re (integrable_gaussKernelC ν hv (e : ℂ))

/-- **Smoothness.** For a finite measure `ν` and `v > 0`, `gaussConv ν v` is `C^∞`. -/
theorem contDiff_gaussConv (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    ContDiff ℝ ∞ (gaussConv ν v) := by
  have hG : ContDiff ℝ ∞ (gaussConvC ν v) :=
    ((differentiable_gaussConvC ν hv).contDiff).restrict_scalars ℝ
  have h1 : ContDiff ℝ ∞ (fun e : ℝ => (gaussConvC ν v (e : ℂ)).re) :=
    Complex.reCLM.contDiff.comp (hG.comp Complex.ofRealCLM.contDiff)
  have heq : gaussConv ν v = fun e : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ *
      (gaussConvC ν v (e : ℂ)).re := funext (gaussConv_eq_re ν hv)
  rw [heq]
  exact contDiff_const.mul h1

theorem gaussianPDFReal_le (y : ℝ) (v : ℝ≥0) (e : ℝ) :
    gaussianPDFReal y v e ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  have h : Real.exp (-(e - y) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (e - y)]) (by positivity)
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(e - y) ^ 2 / (2 * (v : ℝ)))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := mul_one _

theorem continuous_gaussianPDFReal_uncurry (v : ℝ≥0) :
    Continuous (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2) := by
  simp only [gaussianPDFReal_def]
  fun_prop

theorem integrable_gaussianPDFReal_param (ν : Measure ℝ) [IsFiniteMeasure ν] (v : ℝ≥0) (e : ℝ) :
    Integrable (fun y => gaussianPDFReal y v e) ν :=
  (integrable_const ((Real.sqrt (2 * Real.pi * v))⁻¹)).mono'
    ((continuous_gaussianPDFReal_uncurry v).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact gaussianPDFReal_le y v e)

/-- **Strict positivity** for `ν ≠ 0`, `v > 0`. -/
theorem gaussConv_pos (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (e : ℝ) : 0 < gaussConv ν v e := by
  unfold gaussConv
  rw [integral_pos_iff_support_of_nonneg (fun y => gaussianPDFReal_nonneg _ _ _)
    (integrable_gaussianPDFReal_param ν v e)]
  have hs : Function.support (fun y => gaussianPDFReal y v e) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (gaussianPDFReal_pos _ _ _ (by exact_mod_cast hv.ne')).ne'
  rw [hs, Measure.measure_univ_pos]
  exact hν

theorem gaussConv_nonneg (ν : Measure ℝ) (v : ℝ≥0) (e : ℝ) : 0 ≤ gaussConv ν v e :=
  integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _

/-- **Density identity.** `∫ N(y,v)(S) dν(y) = ∫_S gaussConv ν v` for measurable `S`. -/
theorem lintegral_gaussianReal_eq_withDensity (ν : Measure ℝ) [IsFiniteMeasure ν] {v : ℝ≥0}
    (hv : v ≠ 0) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ y, gaussianReal y v S ∂ν =
      volume.withDensity (fun e => ENNReal.ofReal (gaussConv ν v e)) S := by
  rw [withDensity_apply _ hS]
  simp_rw [gaussianReal_apply _ hv S, gaussianPDF_def]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro e
    unfold gaussConv
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal_param ν v e)
      (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg _ _ _)]
  · exact (ENNReal.measurable_ofReal.comp
      (continuous_gaussianPDFReal_uncurry v).measurable).aemeasurable

end BlockBand.Density
