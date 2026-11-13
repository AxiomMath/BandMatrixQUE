module

public import Mathlib
public import BlockBand.External.Johansson.SourceStatement

/-!
# Shifting the vertical `w`-line

How the vertical integral `V_L(z)` in Johansson's double contour kernel changes when the
`w`-line `Re w = L` is moved.

* `verticalIntegral_shift`: no crossing. If `Re z < min L L'` then `V_L(z) = V_{L'}(z)`.
* `verticalIntegral_cross`: crossing the simple pole `w = z`. If `L' < Re z < L` and
  `z ∉ {d_j}` then `V_L(z) - V_{L'}(z) = 2πi · exp((u-v) z / S)`.

Both are deduced from general statements about the Cauchy transform
`cauchyLine a L z = ∫_y i · a(L+iy)/(L+iy-z)` of an entire function `a` with Gaussian decay
on vertical strips (`VerticalGaussian`): `cauchyLine_shift` (rectangle Cauchy theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, horizontal edges `O(e^{-cT²})`),
`cauchyLine_cross` (rectangle theorem for `dslope a z`, plus the exact integral
`∫ i/(α+is) - i/(-β+is) ds = 2πi`), and `differentiableOn_cauchyLine` (holomorphy on
`Re z < L`, by differentiation under the integral sign). The Johansson integrand factors as
`kernelIntegrand = sourceFactor(z) · lineAmplitude(w)/(w-z)` (`kernelIntegrand_eq_factor`)
and `lineAmplitude` is vertically Gaussian with rate `1/(4S)`.

`Johansson.SourceContract` is not used. All statements are exact identities for each fixed
`(S, d, u, v, L, L', z)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Filter Topology
open BlockBand.External
open scoped NNReal

/-!
## Cauchy transforms along vertical lines
-/

/-- Gaussian decay of `a` on every vertical strip `|Re w| ≤ M`, at rate `c`. -/
def VerticalGaussian (a : ℂ → ℂ) (c : ℝ) : Prop :=
  ∀ M : ℝ, ∃ K : ℝ, ∀ x y : ℝ, |x| ≤ M →
    ‖a ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K * Real.exp (-c * y ^ 2)

/-- Cauchy transform of `a` along the upward line `Re w = L` (`dw = i dy`). -/
def cauchyLine (a : ℂ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) / ((L : ℂ) + (y : ℂ) * Complex.I - z))

theorem abs_re_sub_le_norm_line (L y : ℝ) (z : ℂ) :
    |L - z.re| ≤ ‖(L : ℂ) + (y : ℂ) * Complex.I - z‖ := by
  have h : ((L : ℂ) + (y : ℂ) * Complex.I - z).re = L - z.re := by simp
  rw [← h]
  exact Complex.abs_re_le_norm _

theorem abs_im_sub_le_norm_line (x T : ℝ) (z : ℂ) :
    |T - z.im| ≤ ‖(x : ℂ) + (T : ℂ) * Complex.I - z‖ := by
  have h : ((x : ℂ) + (T : ℂ) * Complex.I - z).im = T - z.im := by simp
  rw [← h]
  exact Complex.abs_im_le_norm _

theorem line_sub_ne_zero (L y : ℝ) (z : ℂ) (hz : z.re ≠ L) :
    (L : ℂ) + (y : ℂ) * Complex.I - z ≠ 0 := by
  intro h
  have := abs_re_sub_le_norm_line L y z
  rw [h, norm_zero] at this
  have h2 : 0 < |L - z.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
  linarith

theorem verticalGaussian_const_nonneg {a : ℂ → ℂ} {c M K : ℝ} (hM : 0 ≤ M)
    (hK : ∀ x y : ℝ, |x| ≤ M → ‖a ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K * Real.exp (-c * y ^ 2)) :
    0 ≤ K := by
  have h := hK 0 0 (by simpa using hM)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, mul_one] at h
  exact (norm_nonneg _).trans h

/-- The Cauchy-line integrand is Lebesgue integrable off the line. -/
theorem integrable_cauchyLine {a : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (ha : Continuous a)
    (hG : VerticalGaussian a c) (L : ℝ) (z : ℂ) (hz : z.re ≠ L) :
    Integrable (fun y : ℝ => Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) /
      ((L : ℂ) + (y : ℂ) * Complex.I - z))) := by
  obtain ⟨K, hK⟩ := hG |L|
  have hδ : 0 < |L - z.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
  refine ((integrable_exp_neg_mul_sq hc).const_mul (K / |L - z.re|)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · apply Continuous.aestronglyMeasurable
    apply continuous_const.mul
    exact Continuous.div (ha.comp (by fun_prop)) (by fun_prop)
      (fun y => line_sub_ne_zero L y z hz)
  · rw [norm_mul, Complex.norm_I, one_mul, norm_div]
    have h1 := hK L y le_rfl
    have h2 := abs_re_sub_le_norm_line L y z
    calc ‖a ((L : ℂ) + (y : ℂ) * Complex.I)‖ / ‖(L : ℂ) + (y : ℂ) * Complex.I - z‖
        ≤ K * Real.exp (-c * y ^ 2) / |L - z.re| :=
          div_le_div₀ ((norm_nonneg _).trans h1) h1 hδ h2
      _ = K / |L - z.re| * Real.exp (-c * y ^ 2) := by ring

theorem tendsto_exp_neg_mul_sq_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.exp (-c * T ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => c * T ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hc
  have h2 : Tendsto (fun T : ℝ => -c * T ^ 2) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp h1).congr (fun T => by simp [Function.comp, neg_mul])
  exact Real.tendsto_exp_atBot.comp h2

/-- The symmetric truncations of an integrable vertical integrand converge. -/
theorem tendsto_symm_intervalIntegral {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, f y) atTop (𝓝 (∫ y, f y)) :=
  intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

/-- **Line shift without crossing.** For `a` entire and vertically Gaussian, the Cauchy
transform along `Re w = L` does not depend on `L` as long as `Re z < min L L'`. -/
theorem cauchyLine_shift {a : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (ha : Differentiable ℂ a)
    (hG : VerticalGaussian a c) (L L' : ℝ) (z : ℂ) (hz : z.re < min L L') :
    cauchyLine a L z = cauchyLine a L' z := by
  set f : ℂ → ℂ := fun w => a w / (w - z) with hf
  have hzL : z.re < L := lt_of_lt_of_le hz (min_le_left _ _)
  have hzL' : z.re < L' := lt_of_lt_of_le hz (min_le_right _ _)
  have hfd : ∀ w : ℂ, z.re < w.re → DifferentiableAt ℂ f w := by
    intro w hw
    refine (ha w).div (differentiableAt_id.sub_const z) ?_
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hrect : ∀ T : ℝ,
      (((∫ x in L..L', f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L..L', f ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I • ∫ y in (-T)..T, f ((L' : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • ∫ y in (-T)..T, f ((L : ℂ) + (y : ℂ) * Complex.I) = 0 := by
    intro T
    have hd : DifferentiableOn ℂ f
        (Set.uIcc (⟨L, -T⟩ : ℂ).re (⟨L', T⟩ : ℂ).re ×ℂ
          Set.uIcc (⟨L, -T⟩ : ℂ).im (⟨L', T⟩ : ℂ).im) := by
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply hfd
      have h1 := (Complex.mem_reProdIm.mp hw).1
      have h2 : min L L' ≤ w.re := by
        rcases Set.mem_uIcc.mp h1 with h | h
        · exact (min_le_left _ _).trans h.1
        · exact (min_le_right _ _).trans h.1
      linarith
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨L, -T⟩ ⟨L', T⟩ hd
  -- horizontal edges
  obtain ⟨K, hK⟩ := hG (|L| + |L'|)
  set δ : ℝ := min L L' - z.re with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hedge : ∀ s : ℝ, ‖∫ x in L..L', f ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤
      K * Real.exp (-c * s ^ 2) / δ * |L' - L| := by
    intro s
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.uIcc L L' := Set.uIoc_subset_uIcc hx
    have hxM : |x| ≤ |L| + |L'| := by
      rcases Set.mem_uIcc.mp hx' with h | h
      · rw [abs_le]; constructor <;>
          linarith [neg_abs_le L, le_abs_self L', abs_nonneg L, abs_nonneg L', neg_abs_le L',
            le_abs_self L]
      · rw [abs_le]; constructor <;>
          linarith [neg_abs_le L, le_abs_self L', abs_nonneg L, abs_nonneg L', neg_abs_le L',
            le_abs_self L]
    have hxre : min L L' ≤ x := by
      rcases Set.mem_uIcc.mp hx' with h | h
      · exact (min_le_left _ _).trans h.1
      · exact (min_le_right _ _).trans h.1
    have h1 := hK x s hxM
    have h2 : δ ≤ ‖(x : ℂ) + (s : ℂ) * Complex.I - z‖ := by
      have := abs_re_sub_le_norm_line x s z
      have h3 : δ ≤ |x - z.re| := by
        rw [abs_of_pos (by linarith)]; linarith
      linarith
    simp only [hf, norm_div]
    exact div_le_div₀ ((norm_nonneg _).trans h1) h1 hδ0 h2
  have hE := tendsto_exp_neg_mul_sq_atTop hc
  have hB : Tendsto (fun T : ℝ =>
      ((∫ x in L..L', f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L..L', f ((x : ℂ) + (T : ℂ) * Complex.I))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => 2 * (K * Real.exp (-c * T ^ 2) / δ * |L' - L|))
        atTop (𝓝 0) := by
      have := ((hE.const_mul K).div_const δ).mul_const |L' - L|
      simpa using this.const_mul 2
    refine squeeze_zero_norm (fun T => ?_) hlim
    refine (norm_sub_le _ _).trans ?_
    have e1 := hedge (-T)
    have e2 := hedge T
    rw [show (-T) ^ 2 = T ^ 2 by ring] at e1
    linarith
  -- vertical parts
  have hIL := integrable_cauchyLine hc ha.continuous hG L z (ne_of_lt hzL)
  have hIL' := integrable_cauchyLine hc ha.continuous hG L' z (ne_of_lt hzL')
  have hV : Tendsto (fun T : ℝ =>
      Complex.I • (∫ y in (-T)..T, f ((L' : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • ∫ y in (-T)..T, f ((L : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (cauchyLine a L' z - cauchyLine a L z)) := by
    have h1 := tendsto_symm_intervalIntegral hIL'
    have h2 := tendsto_symm_intervalIntegral hIL
    refine (h1.sub h2).congr (fun T => ?_)
    simp only [smul_eq_mul, hf]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hV' : Tendsto (fun T : ℝ =>
      Complex.I • (∫ y in (-T)..T, f ((L' : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • ∫ y in (-T)..T, f ((L : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
    have := hB.neg
    rw [neg_zero] at this
    refine this.congr (fun T => ?_)
    have h := hrect T
    linear_combination -h
  have := tendsto_nhds_unique hV hV'
  linear_combination -this

/-!
## Crossing the pole `w = z`
-/

theorem line_inv_sum (α s : ℝ) (hα : α ≠ 0) :
    ((α : ℂ) + (s : ℂ) * Complex.I)⁻¹ + ((α : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹ =
      ((2 * α / (α ^ 2 + s ^ 2) : ℝ) : ℂ) := by
  have h1 : (α : ℂ) + (s : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact hα this
  have h2 : (α : ℂ) + ((-s : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact hα this
  have hpos : (α ^ 2 + s ^ 2 : ℝ) ≠ 0 := by positivity
  have hprod : ((α : ℂ) + (s : ℂ) * Complex.I) * ((α : ℂ) + ((-s : ℝ) : ℂ) * Complex.I) =
      ((α ^ 2 + s ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [pow_two]
    · simp [pow_two]; ring
  rw [inv_add_inv h1 h2, hprod]
  have : (α : ℂ) + (s : ℂ) * Complex.I + ((α : ℂ) + ((-s : ℝ) : ℂ) * Complex.I) =
      ((2 * α : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_div]

/-- `∫ α/(α²+s²) ds = π` for `α > 0`. -/
theorem integral_poisson_kernel (α : ℝ) (hα : 0 < α) :
    ∫ s : ℝ, α / (α ^ 2 + s ^ 2) = Real.pi := by
  have h := Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) α
  rw [integral_univ_inv_one_add_sq, abs_of_pos hα, smul_eq_mul] at h
  have he : (fun s : ℝ => α / (α ^ 2 + s ^ 2)) = fun s => α⁻¹ * (1 + (s / α) ^ 2)⁻¹ := by
    funext s
    field_simp
  rw [he, integral_const_mul, h]
  field_simp

theorem integrable_poisson_kernel (α : ℝ) (hα : 0 < α) :
    Integrable (fun s : ℝ => (α ^ 2 + s ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq.comp_div hα.ne').const_mul (α ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only
  field_simp

/-- The difference of the two resolvent lines `Re = α > 0` and `Re = -β < 0`. -/
def resolventLineDiff (α β s : ℝ) : ℂ :=
  Complex.I * ((α : ℂ) + (s : ℂ) * Complex.I)⁻¹ -
    Complex.I * (((-β : ℝ) : ℂ) + (s : ℂ) * Complex.I)⁻¹

theorem integrable_resolventLineDiff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Integrable (resolventLineDiff α β) := by
  set m : ℝ := min α β with hm
  have hm0 : 0 < m := lt_min hα hβ
  have hmα : m ≤ α := min_le_left _ _
  have hmβ : m ≤ β := min_le_right _ _
  refine ((integrable_poisson_kernel m hm0).const_mul (α + β)).mono' ?_
    (Eventually.of_forall fun s => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold resolventLineDiff
    apply Continuous.sub
    · apply continuous_const.mul
      apply Continuous.inv₀ (by fun_prop)
      intro s h; have := congrArg Complex.re h; simp at this; linarith
    · apply continuous_const.mul
      apply Continuous.inv₀ (by fun_prop)
      intro s h; have := congrArg Complex.re h; simp at this; linarith
  · set p : ℂ := (α : ℂ) + (s : ℂ) * Complex.I
    set q : ℂ := ((-β : ℝ) : ℂ) + (s : ℂ) * Complex.I
    have hp : p ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [p] at this; linarith
    have hq : q ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [q] at this; linarith
    have hqp : q - p = -((α + β : ℝ) : ℂ) := by
      simp only [p, q]; push_cast; ring
    have heq : resolventLineDiff α β s = -Complex.I * ((α + β : ℝ) : ℂ) * (p * q)⁻¹ := by
      show Complex.I * p⁻¹ - Complex.I * q⁻¹ = _
      calc Complex.I * p⁻¹ - Complex.I * q⁻¹
          = Complex.I * ((q * q⁻¹) * p⁻¹ - (p * p⁻¹) * q⁻¹) := by
            rw [mul_inv_cancel₀ hq, mul_inv_cancel₀ hp]; ring
        _ = Complex.I * (q - p) * (p * q)⁻¹ := by rw [mul_inv]; ring
        _ = _ := by rw [hqp]; ring
    have hnp : ‖p‖ ^ 2 = α ^ 2 + s ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have hnq : ‖q‖ ^ 2 = β ^ 2 + s ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]; ring
    have hlow : m ^ 2 + s ^ 2 ≤ ‖p‖ * ‖q‖ := by
      have hsq : (m ^ 2 + s ^ 2) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
        rw [mul_pow, hnp, hnq]
        have h1 : m ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ hm0.le hmα 2
        have h2 : m ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hm0.le hmβ 2
        have h3 : 0 ≤ m ^ 2 + s ^ 2 := by positivity
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have hpos : 0 < m ^ 2 + s ^ 2 := by positivity
    rw [heq, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith), norm_inv, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact inv_anti₀ hpos hlow

theorem integral_resolventLineDiff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ s : ℝ, resolventLineDiff α β s = 2 * Real.pi * Complex.I := by
  have hint := integrable_resolventLineDiff α β hα hβ
  have hneg : ∫ s : ℝ, resolventLineDiff α β (-s) = ∫ s : ℝ, resolventLineDiff α β s :=
    integral_neg_eq_self _ _
  have hsum : ∀ s : ℝ, resolventLineDiff α β s + resolventLineDiff α β (-s) =
      2 * Complex.I * (((α / (α ^ 2 + s ^ 2) + β / (β ^ 2 + s ^ 2)) : ℝ) : ℂ) := by
    intro s
    have h1 := line_inv_sum α s hα.ne'
    have h2 := line_inv_sum (-β) s (by linarith)
    calc resolventLineDiff α β s + resolventLineDiff α β (-s)
        = Complex.I * (((α : ℂ) + (s : ℂ) * Complex.I)⁻¹ +
              ((α : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) -
            Complex.I * ((((-β : ℝ) : ℂ) + (s : ℂ) * Complex.I)⁻¹ +
              (((-β : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) := by
          unfold resolventLineDiff; ring
      _ = Complex.I * ((2 * α / (α ^ 2 + s ^ 2) : ℝ) : ℂ) -
            Complex.I * ((2 * (-β) / ((-β) ^ 2 + s ^ 2) : ℝ) : ℂ) := by rw [h1, h2]
      _ = _ := by push_cast; ring
  have hint2 : Integrable (fun s : ℝ => resolventLineDiff α β (-s)) := hint.comp_neg
  have hP : ∀ γ : ℝ, 0 < γ → Integrable (fun s : ℝ => γ / (γ ^ 2 + s ^ 2)) := fun γ hγ =>
    ((integrable_poisson_kernel γ hγ).const_mul γ).congr
      (Eventually.of_forall fun s => by simp [div_eq_mul_inv])
  have htot : ∫ s : ℝ, (resolventLineDiff α β s + resolventLineDiff α β (-s)) =
      2 * (2 * Real.pi * Complex.I) := by
    rw [integral_congr_ae (Eventually.of_forall hsum), integral_const_mul, integral_complex_ofReal,
      integral_add (hP α hα) (hP β hβ), integral_poisson_kernel α hα,
      integral_poisson_kernel β hβ]
    push_cast
    ring
  rw [integral_add hint hint2, hneg] at htot
  linear_combination htot / 2

theorem continuous_resolventLineDiff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Continuous (resolventLineDiff α β) := by
  unfold resolventLineDiff
  apply Continuous.sub
  · apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro s h; have := congrArg Complex.re h; simp at this; linarith
  · apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro s h; have := congrArg Complex.re h; simp at this; linarith

theorem line_sub_eq (L y : ℝ) (z : ℂ) :
    (L : ℂ) + (y : ℂ) * Complex.I - z =
      ((L - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- **Line shift across the pole.** For `a` entire and vertically Gaussian and
`L' < Re z < L`, the two Cauchy transforms differ by the residue `2πi a(z)`. -/
theorem cauchyLine_cross {a : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (ha : Differentiable ℂ a)
    (hG : VerticalGaussian a c) (L L' : ℝ) (z : ℂ) (hL' : L' < z.re) (hL : z.re < L) :
    cauchyLine a L z - cauchyLine a L' z = 2 * Real.pi * Complex.I * a z := by
  set φ : ℂ → ℂ := dslope a z with hφ
  have hφd : Differentiable ℂ φ := by
    have := (Complex.differentiableOn_dslope (f := a) (s := Set.univ) (c := z)
      Filter.univ_mem).mpr ha.differentiableOn
    exact differentiableOn_univ.mp this
  have hφeq : ∀ w : ℂ, w ≠ z → φ w = (a w - a z) / (w - z) := by
    intro w hw
    rw [hφ, dslope_of_ne _ hw, slope_def_field]
  have hsplit : ∀ w : ℂ, w ≠ z → a w / (w - z) = φ w + a z * (w - z)⁻¹ := by
    intro w hw
    rw [hφeq w hw]
    have : w - z ≠ 0 := sub_ne_zero.mpr hw
    field_simp
    ring
  have hrect : ∀ T : ℝ,
      (((∫ x in L'..L, φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L'..L, φ ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I • ∫ y in (-T)..T, φ ((L : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • ∫ y in (-T)..T, φ ((L' : ℂ) + (y : ℂ) * Complex.I) = 0 := fun T =>
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ ⟨L', -T⟩ ⟨L, T⟩
      hφd.differentiableOn
  -- horizontal edges of the rectangle for `φ`
  obtain ⟨K, hK⟩ := hG (|L| + |L'|)
  have hK0 : 0 ≤ K := verticalGaussian_const_nonneg (by positivity) hK
  set m : ℝ := |z.im| with hm
  have hedge : ∀ s : ℝ, m < |s| → ‖∫ x in L'..L, φ ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤
      (K + ‖a z‖) / (|s| - m) * |L - L'| := by
    intro s hs
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.uIcc L' L := Set.uIoc_subset_uIcc hx
    have hxM : |x| ≤ |L| + |L'| := by
      rcases Set.mem_uIcc.mp hx' with h | h
      · rw [abs_le]; constructor <;>
          linarith [neg_abs_le L, le_abs_self L', abs_nonneg L, abs_nonneg L', neg_abs_le L',
            le_abs_self L]
      · rw [abs_le]; constructor <;>
          linarith [neg_abs_le L, le_abs_self L', abs_nonneg L, abs_nonneg L', neg_abs_le L',
            le_abs_self L]
    have hdist : |s| - m ≤ ‖(x : ℂ) + (s : ℂ) * Complex.I - z‖ := by
      have h1 := abs_im_sub_le_norm_line x s z
      have h2 := abs_sub_abs_le_abs_sub s z.im
      linarith
    have hpos : 0 < |s| - m := by linarith
    have hne : (x : ℂ) + (s : ℂ) * Complex.I ≠ z := by
      intro h
      have := hdist
      rw [h, sub_self, norm_zero] at this
      linarith
    have haw : ‖a ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ K := by
      have h1 := hK x s hxM
      have h2 : Real.exp (-c * s ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c * s ^ 2 := by positivity
        linarith
      nlinarith
    rw [hφeq _ hne, norm_div]
    refine div_le_div₀ (by positivity) ?_ hpos hdist
    exact (norm_sub_le _ _).trans (by linarith)
  have hB : Tendsto (fun T : ℝ =>
      ((∫ x in L'..L, φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L'..L, φ ((x : ℂ) + (T : ℂ) * Complex.I))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun T : ℝ => (T + -m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-m) tendsto_id)
    have hlim : Tendsto (fun T : ℝ => 2 * ((K + ‖a z‖) * |L - L'|) * (T + -m)⁻¹)
        atTop (𝓝 0) := by
      simpa using hinv.const_mul (2 * ((K + ‖a z‖) * |L - L'|))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop m] with T hT
    have hT0 : 0 ≤ T := (abs_nonneg _).trans (le_of_lt hT)
    have e1 := hedge (-T) (by rw [abs_neg, abs_of_nonneg hT0]; exact hT)
    have e2 := hedge T (by rw [abs_of_nonneg hT0]; exact hT)
    rw [abs_neg, abs_of_nonneg hT0] at e1
    rw [abs_of_nonneg hT0] at e2
    refine (norm_sub_le _ _).trans ?_
    have : (K + ‖a z‖) / (T - m) * |L - L'| = (K + ‖a z‖) * |L - L'| * (T + -m)⁻¹ := by
      rw [← sub_eq_add_neg]; ring
    rw [this] at e1 e2
    linarith
  -- pointwise splitting on the two lines
  set α : ℝ := L - z.re with hα
  set β : ℝ := z.re - L' with hβ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hzL : z.re ≠ L := ne_of_lt hL
  have hzL' : z.re ≠ L' := ne_of_gt hL'
  have hpt : ∀ y : ℝ,
      Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) / ((L : ℂ) + (y : ℂ) * Complex.I - z)) -
        Complex.I * (a ((L' : ℂ) + (y : ℂ) * Complex.I) /
          ((L' : ℂ) + (y : ℂ) * Complex.I - z)) =
      (Complex.I * φ ((L : ℂ) + (y : ℂ) * Complex.I) -
          Complex.I * φ ((L' : ℂ) + (y : ℂ) * Complex.I)) +
        a z * resolventLineDiff α β (y - z.im) := by
    intro y
    have h1 : (L : ℂ) + (y : ℂ) * Complex.I ≠ z := fun h =>
      line_sub_ne_zero L y z hzL (by rw [h, sub_self])
    have h2 : (L' : ℂ) + (y : ℂ) * Complex.I ≠ z := fun h =>
      line_sub_ne_zero L' y z hzL' (by rw [h, sub_self])
    rw [hsplit _ h1, hsplit _ h2, line_sub_eq L y z, line_sub_eq L' y z]
    unfold resolventLineDiff
    have : ((L' - z.re : ℝ) : ℂ) = ((-β : ℝ) : ℂ) := by rw [hβ]; push_cast; ring
    rw [this, ← hα]
    ring
  have hcL : Continuous (fun y : ℝ => Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) /
      ((L : ℂ) + (y : ℂ) * Complex.I - z))) :=
    continuous_const.mul (Continuous.div (ha.continuous.comp (by fun_prop)) (by fun_prop)
      (fun y => line_sub_ne_zero L y z hzL))
  have hcL' : Continuous (fun y : ℝ => Complex.I * (a ((L' : ℂ) + (y : ℂ) * Complex.I) /
      ((L' : ℂ) + (y : ℂ) * Complex.I - z))) :=
    continuous_const.mul (Continuous.div (ha.continuous.comp (by fun_prop)) (by fun_prop)
      (fun y => line_sub_ne_zero L' y z hzL'))
  have hcφL : Continuous (fun y : ℝ => φ ((L : ℂ) + (y : ℂ) * Complex.I)) :=
    hφd.continuous.comp (by fun_prop)
  have hcφL' : Continuous (fun y : ℝ => φ ((L' : ℂ) + (y : ℂ) * Complex.I)) :=
    hφd.continuous.comp (by fun_prop)
  have hcR : Continuous (fun y : ℝ => resolventLineDiff α β (y - z.im)) :=
    (continuous_resolventLineDiff α β hα0 hβ0).comp (by fun_prop)
  have hT : ∀ T : ℝ,
      (∫ y in (-T)..T, Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) /
          ((L : ℂ) + (y : ℂ) * Complex.I - z))) -
        (∫ y in (-T)..T, Complex.I * (a ((L' : ℂ) + (y : ℂ) * Complex.I) /
          ((L' : ℂ) + (y : ℂ) * Complex.I - z))) =
      -(((∫ x in L'..L, φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L'..L, φ ((x : ℂ) + (T : ℂ) * Complex.I))) +
        a z * ∫ y in (-T)..T, resolventLineDiff α β (y - z.im) := by
    intro T
    rw [← intervalIntegral.integral_sub (hcL.intervalIntegrable _ _)
      (hcL'.intervalIntegrable _ _)]
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun y : ℝ => Complex.I * φ ((L : ℂ) + (y : ℂ) * Complex.I) -
        Complex.I * φ ((L' : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
      ((continuous_const.mul hcφL).sub (continuous_const.mul hcφL')).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun y : ℝ => a z * resolventLineDiff α β (y - z.im))
        volume (-T) T := (continuous_const.mul hcR).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun y : ℝ => Complex.I * φ ((L : ℂ) + (y : ℂ) * Complex.I))
        volume (-T) T := (continuous_const.mul hcφL).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun y : ℝ => Complex.I * φ ((L' : ℂ) + (y : ℂ) * Complex.I))
        volume (-T) T := (continuous_const.mul hcφL').intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_sub i3 i4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have h := hrect T
    simp only [smul_eq_mul] at h
    linear_combination h
  have hRint : Integrable (fun y : ℝ => resolventLineDiff α β (y - z.im)) :=
    (integrable_resolventLineDiff α β hα0 hβ0).comp_sub_right z.im
  have hRval : ∫ y : ℝ, resolventLineDiff α β (y - z.im) = 2 * Real.pi * Complex.I :=
    (integral_sub_right_eq_self (resolventLineDiff α β) z.im).trans
      (integral_resolventLineDiff α β hα0 hβ0)
  have hlim1 := (tendsto_symm_intervalIntegral
      (integrable_cauchyLine hc ha.continuous hG L z hzL)).sub
    (tendsto_symm_intervalIntegral (integrable_cauchyLine hc ha.continuous hG L' z hzL'))
  have hlim2 : Tendsto (fun T : ℝ =>
      -(((∫ x in L'..L, φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in L'..L, φ ((x : ℂ) + (T : ℂ) * Complex.I))) +
        a z * ∫ y in (-T)..T, resolventLineDiff α β (y - z.im)) atTop
      (𝓝 (-0 + a z * (2 * Real.pi * Complex.I))) := by
    refine hB.neg.add (Tendsto.const_mul _ ?_)
    rw [← hRval]
    exact tendsto_symm_intervalIntegral hRint
  have := tendsto_nhds_unique (hlim1.congr hT) hlim2
  unfold cauchyLine
  rw [this]
  ring

/-- **Holomorphy of the Cauchy transform** on the open half-plane `Re z < L`. -/
theorem differentiableOn_cauchyLine {a : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (ha : Differentiable ℂ a)
    (hG : VerticalGaussian a c) (L : ℝ) :
    DifferentiableOn ℂ (cauchyLine a L) {z : ℂ | z.re < L} := by
  intro z₀ hz₀
  have hz₀' : z₀.re < L := hz₀
  apply DifferentiableAt.differentiableWithinAt
  set δ : ℝ := L - z₀.re with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨K, hK⟩ := hG |L|
  set F : ℂ → ℝ → ℂ := fun z y => Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) /
    ((L : ℂ) + (y : ℂ) * Complex.I - z)) with hF
  set F' : ℂ → ℝ → ℂ := fun z y => Complex.I * (a ((L : ℂ) + (y : ℂ) * Complex.I) /
    ((L : ℂ) + (y : ℂ) * Complex.I - z) ^ 2) with hF'
  have hball : ∀ z ∈ Metric.ball z₀ (δ / 2), δ / 2 ≤ L - z.re := by
    intro z hz
    have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖z - z₀‖ < δ / 2 := by rw [← dist_eq_norm]; exact hz
    have h3 := le_abs_self (z.re - z₀.re)
    linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) := by
    intro z
    have hcont : Continuous (fun y : ℝ => a ((L : ℂ) + (y : ℂ) * Complex.I)) :=
      ha.continuous.comp (by fun_prop)
    have : Measurable (F z) := by
      simp only [hF]
      exact measurable_const.mul (hcont.measurable.div (by fun_prop))
    exact this.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' z₀) := by
    have hcont : Continuous (fun y : ℝ => a ((L : ℂ) + (y : ℂ) * Complex.I)) :=
      ha.continuous.comp (by fun_prop)
    have : Measurable (F' z₀) := by
      simp only [hF']
      exact measurable_const.mul (hcont.measurable.div (by fun_prop))
    exact this.aestronglyMeasurable
  have hbound : ∀ y : ℝ, ∀ z ∈ Metric.ball z₀ (δ / 2),
      ‖F' z y‖ ≤ K / (δ / 2) ^ 2 * Real.exp (-c * y ^ 2) := by
    intro y z hz
    have h1 := hK L y le_rfl
    have h2 : δ / 2 ≤ ‖(L : ℂ) + (y : ℂ) * Complex.I - z‖ := by
      have := abs_re_sub_le_norm_line L y z
      have h3 := hball z hz
      have h4 : L - z.re ≤ |L - z.re| := le_abs_self _
      linarith
    simp only [hF', norm_mul, Complex.norm_I, one_mul, norm_div, norm_pow]
    calc ‖a ((L : ℂ) + (y : ℂ) * Complex.I)‖ / ‖(L : ℂ) + (y : ℂ) * Complex.I - z‖ ^ 2
        ≤ K * Real.exp (-c * y ^ 2) / (δ / 2) ^ 2 :=
          div_le_div₀ ((norm_nonneg _).trans h1) h1 (by positivity)
            (pow_le_pow_left₀ (by positivity) h2 2)
      _ = K / (δ / 2) ^ 2 * Real.exp (-c * y ^ 2) := by ring
  have hderiv : ∀ y : ℝ, ∀ z ∈ Metric.ball z₀ (δ / 2),
      HasDerivAt (fun z => F z y) (F' z y) z := by
    intro y z hz
    have hne : (L : ℂ) + (y : ℂ) * Complex.I - z ≠ 0 := by
      apply line_sub_ne_zero
      have := hball z hz
      linarith
    have h1 : HasDerivAt (fun z : ℂ => (L : ℂ) + (y : ℂ) * Complex.I - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub ((L : ℂ) + (y : ℂ) * Complex.I)
    have h2 := (h1.inv hne).const_mul (Complex.I * a ((L : ℂ) + (y : ℂ) * Complex.I))
    simp only [hF, hF']
    convert h2 using 1
    · funext z
      simp only [Pi.inv_apply, div_eq_mul_inv]
      ring
    · simp only [neg_neg, div_eq_mul_inv]
      ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (x₀ := z₀) (bound := fun y => K / (δ / 2) ^ 2 * Real.exp (-c * y ^ 2))
    (Metric.ball_mem_nhds z₀ (by positivity)) (Eventually.of_forall hmeas)
    (integrable_cauchyLine hc ha.continuous hG L z₀ (ne_of_lt hz₀')) hmeas'
    (Eventually.of_forall hbound) ((integrable_exp_neg_mul_sq hc).const_mul _)
    (Eventually.of_forall hderiv)
  exact hres.2.differentiableAt

/-!
## The Johansson integrand
-/

/-- The `w`-amplitude of the Johansson kernel: `exp((w²-2vw)/(2S)) ∏_j (w-d_j)`. -/
def lineAmplitude {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (v : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((w ^ 2 - 2 * (v : ℂ) * w) / (2 * (S : ℂ))) * ∏ j, (w - (d j : ℂ))

/-- The `z`-factor of the Johansson kernel: `exp((2uz-z²)/(2S)) / ∏_j (z-d_j)`. -/
def sourceFactor {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-z ^ 2 + 2 * (u : ℂ) * z) / (2 * (S : ℂ))) / ∏ j, (z - (d j : ℂ))

theorem kernelIntegrand_eq_factor {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v : ℝ) (z w : ℂ) :
    Johansson.kernelIntegrand S d u v z w = sourceFactor S d u z * (lineAmplitude S d v w / (w - z)) := by
  unfold Johansson.kernelIntegrand sourceFactor lineAmplitude
  rw [Finset.prod_div_distrib,
    show (w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z) / (2 * (S : ℂ)) =
      (w ^ 2 - 2 * (v : ℂ) * w) / (2 * (S : ℂ)) + (-z ^ 2 + 2 * (u : ℂ) * z) / (2 * (S : ℂ)) by
        ring, Complex.exp_add]
  ring

/-- `V_L(z) = sourceFactor(z) · cauchyLine(lineAmplitude)(L, z)`, exactly. -/
theorem verticalIntegral_eq_factor {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v L : ℝ) (z : ℂ) :
    Johansson.verticalIntegral S d u v L z =
      sourceFactor S d u z * cauchyLine (lineAmplitude S d v) L z := by
  unfold Johansson.verticalIntegral cauchyLine
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [kernelIntegrand_eq_factor]
  ring

theorem differentiable_lineAmplitude {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (v : ℝ) :
    Differentiable ℂ (lineAmplitude S d v) := by
  unfold lineAmplitude
  fun_prop

/-- Gaussian decay of the amplitude on vertical strips, rate `1/(4S)`. -/
theorem lineAmplitude_verticalGaussian {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) (v : ℝ) :
    VerticalGaussian (lineAmplitude S d v) (1 / (4 * S)) := by
  intro M
  have hSr : (0 : ℝ) < S := hS
  set D : ℝ := ∑ j, |d j| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hdD : ∀ j, |d j| ≤ D := fun j =>
    Finset.single_le_sum (f := fun j => |d j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  set A : ℝ := |M| + D + 1 with hA
  refine ⟨Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S)) *
    ((N.factorial : ℝ) * Real.exp (A + A ^ 2 * S)), fun x y hx => ?_⟩
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hw
  have hA1 : 1 ≤ A := by have := abs_nonneg M; linarith
  have hxM : |x| ≤ |M| := hx.trans (le_abs_self M)
  have hexp : ‖Complex.exp ((w ^ 2 - 2 * (v : ℂ) * w) / (2 * ((S : ℝ) : ℂ)))‖ ≤
      Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S) - y ^ 2 / (2 * S)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [show (2 * ((S : ℝ) : ℂ)) = ((2 * (S : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re]
    have hnum : (w ^ 2 - 2 * (v : ℂ) * w).re = x ^ 2 - y ^ 2 - 2 * v * x := by
      simp [hw, sq, Complex.mul_re, Complex.mul_im]
    rw [hnum, ← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs x, ← sq_abs M]; exact pow_le_pow_left₀ (abs_nonneg _) hxM 2
    have h2 : |v * x| ≤ |v| * |M| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxM (abs_nonneg _)
    have h3 := neg_abs_le (v * x)
    nlinarith
  have hprod : ‖∏ j, (w - (d j : ℂ))‖ ≤ (A * (1 + |y|)) ^ N := by
    rw [norm_prod]
    calc ∏ j, ‖w - (d j : ℂ)‖ ≤ ∏ _j : Fin N, (A * (1 + |y|)) := by
          apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
          intro j _
          calc ‖w - (d j : ℂ)‖ ≤ ‖w‖ + ‖(d j : ℂ)‖ := norm_sub_le _ _
            _ ≤ |x| + |y| + |d j| := by
                have : ‖w‖ ≤ |x| + |y| := by
                  calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
                    _ = |x| + |y| := by simp [Complex.norm_real]
                rw [Complex.norm_real, Real.norm_eq_abs]; linarith
            _ ≤ A * (1 + |y|) := by
                have := abs_nonneg y
                have := hdD j
                nlinarith
      _ = (A * (1 + |y|)) ^ N := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpoly : (A * (1 + |y|)) ^ N ≤
      (N.factorial : ℝ) * Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S)) := by
    have hX : 0 ≤ A * (1 + |y|) := by positivity
    have h1 := Real.pow_div_factorial_le_exp (A * (1 + |y|)) hX N
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hfac] at h1
    refine h1.trans ?_
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hfac.le
    apply Real.exp_le_exp.mpr
    have hy := abs_nonneg y
    have key : A * |y| ≤ A ^ 2 * S + y ^ 2 / (4 * S) := by
      rw [← sq_abs y]
      have hid : A ^ 2 * S + |y| ^ 2 / (4 * S) - A * |y| = (2 * A * S - |y|) ^ 2 / (4 * S) := by
        field_simp
        ring
      have : 0 ≤ (2 * A * S - |y|) ^ 2 / (4 * S) := by positivity
      linarith
    nlinarith
  unfold lineAmplitude
  rw [norm_mul]
  have hS2 : ((S : ℂ)) = (((S : ℝ)) : ℂ) := rfl
  rw [hS2]
  calc ‖Complex.exp ((w ^ 2 - 2 * (v : ℂ) * w) / (2 * ((S : ℝ) : ℂ)))‖ *
        ‖∏ j, (w - (d j : ℂ))‖
      ≤ Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S) - y ^ 2 / (2 * S)) *
          ((N.factorial : ℝ) * Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S))) :=
        mul_le_mul hexp (hprod.trans hpoly) (norm_nonneg _) (by positivity)
    _ = Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S)) *
          ((N.factorial : ℝ) * Real.exp (A + A ^ 2 * S)) * Real.exp (-(1 / (4 * S)) * y ^ 2) := by
        have e1 : Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S) - y ^ 2 / (2 * S)) =
            Real.exp ((M ^ 2 + 2 * |v| * |M|) / (2 * S)) * Real.exp (-(y ^ 2 / (2 * S))) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S)) =
            Real.exp (A + A ^ 2 * S) * Real.exp (y ^ 2 / (4 * S)) := by
          rw [← Real.exp_add]
        have e3 : Real.exp (-(y ^ 2 / (2 * S))) * Real.exp (y ^ 2 / (4 * S)) =
            Real.exp (-(1 / (4 * S)) * y ^ 2) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        rw [e1, e2, ← e3]
        ring

/-- **Line shift without crossing.** For `S > 0`, any real
source `d`, real `u, v`, and `Re z < min L L'`: `V_L(z) = V_{L'}(z)`. -/
theorem verticalIntegral_shift {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) (u v L L' : ℝ)
    (z : ℂ) (hz : z.re < min L L') :
    Johansson.verticalIntegral S d u v L z = Johansson.verticalIntegral S d u v L' z := by
  have hSr : (0 : ℝ) < S := hS
  rw [verticalIntegral_eq_factor, verticalIntegral_eq_factor,
    cauchyLine_shift (c := 1 / (4 * S)) (by positivity) (differentiable_lineAmplitude S d v)
      (lineAmplitude_verticalGaussian S hS d v) L L' z hz]

/-- `sourceFactor · lineAmplitude` at the same point is the residue `exp((u-v)z/S)`. -/
theorem sourceFactor_mul_lineAmplitude {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v : ℝ) (z : ℂ)
    (hzd : ∀ j, z ≠ (d j : ℂ)) :
    sourceFactor S d u z * lineAmplitude S d v z = Complex.exp (((u : ℂ) - v) * z / S) := by
  unfold sourceFactor lineAmplitude
  have hP : ∏ j, (z - (d j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hzd j))
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hP, ← Complex.exp_add]
  congr 1
  ring

/-- **Line shift across the pole `w = z`.** For `S > 0`,
any real source `d`, real `u, v`, `L' < Re z < L` and `z ∉ {d_j}`:
`V_L(z) - V_{L'}(z) = 2πi · exp((u - v) z / S)`. -/
theorem verticalIntegral_cross {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) (u v L L' : ℝ)
    (z : ℂ) (hL' : L' < z.re) (hL : z.re < L) (hzd : ∀ j, z ≠ (d j : ℂ)) :
    Johansson.verticalIntegral S d u v L z - Johansson.verticalIntegral S d u v L' z =
      2 * Real.pi * Complex.I * Complex.exp (((u : ℂ) - v) * z / S) := by
  have hSr : (0 : ℝ) < S := hS
  rw [verticalIntegral_eq_factor, verticalIntegral_eq_factor, ← mul_sub,
    cauchyLine_cross (c := 1 / (4 * S)) (by positivity) (differentiable_lineAmplitude S d v)
      (lineAmplitude_verticalGaussian S hS d v) L L' z hL' hL,
    ← sourceFactor_mul_lineAmplitude S d u v z hzd]
  ring

end BlockBand.GaussianBulk
