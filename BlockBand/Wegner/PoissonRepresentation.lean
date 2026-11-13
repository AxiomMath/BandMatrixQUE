module

public import Mathlib

/-!
# Poisson representation at `ζ = i` on the closed upper half-plane

For `f` complex-differentiable and bounded on the closed upper half-plane,
`∫_ℝ (1 + t²)⁻¹ f(t) dt = π f(i)`, proved by showing that the real-axis integral of
`dslope f i (z) · (z + i)⁻¹` vanishes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory Complex Set Filter Topology

/-- The auxiliary function `dslope f i (z) · (z + i)⁻¹`. -/
def poissonAux (f : ℂ → ℂ) (z : ℂ) : ℂ := dslope f I z * (z + I)⁻¹

theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem poissonAux_eq {f : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) (hzI : z ≠ I) :
    poissonAux f z = (1 + z ^ 2)⁻¹ * (f z - f I) := by
  have h1 : z - I ≠ 0 := sub_ne_zero.mpr hzI
  have h2 : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg hz
  have h3 : 1 + z ^ 2 = (z - I) * (z + I) := by
    ring_nf
    rw [I_sq]
    ring
  rw [poissonAux, dslope_of_ne _ hzI, slope_def_field, h3, mul_inv]
  field_simp

section

variable {f : ℂ → ℂ}

theorem continuousAt_poissonAux (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z) {z : ℂ}
    (hz : 0 ≤ z.im) : ContinuousAt (poissonAux f) z := by
  have hinv : ContinuousAt (fun z : ℂ => (z + I)⁻¹) z :=
    (continuousAt_id.add continuousAt_const).inv₀ (add_I_ne_zero_of_im_nonneg hz)
  refine ContinuousAt.mul ?_ hinv
  by_cases hzI : z = I
  · subst hzI
    exact continuousAt_dslope_same.mpr (hf I (by simp))
  · exact (continuousAt_dslope_of_ne hzI).mpr (hf z hz).continuousAt

theorem differentiableOn_poissonAux (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ (poissonAux f) {z : ℂ | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hI : {z : ℂ | 0 < z.im} ∈ 𝓝 I := hopen.mem_nhds (by simp)
  have hd : DifferentiableOn ℂ (dslope f I) {z : ℂ | 0 < z.im} :=
    (Complex.differentiableOn_dslope hI).mpr fun z hz =>
      (hf z (le_of_lt hz)).differentiableWithinAt
  intro z hz
  refine (hd z hz).mul ?_
  exact ((differentiableAt_id.add_const I).inv
    (add_I_ne_zero_of_im_nonneg (le_of_lt hz))).differentiableWithinAt

/-- Off-axis bound: for `R ≥ 2`, `‖z‖ ≥ R`, `Im z ≥ 0`, `‖poissonAux f z‖ ≤ 4M/R²`. -/
theorem norm_poissonAux_le {M : ℝ} (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) {R : ℝ} (hR : 2 ≤ R)
    {z : ℂ} (hz : 0 ≤ z.im) (hzR : R ≤ ‖z‖) : ‖poissonAux f z‖ ≤ 4 * M / R ^ 2 := by
  have hzI : z ≠ I := by
    intro h
    rw [h, norm_I] at hzR
    linarith
  rw [poissonAux_eq hz hzI, norm_mul, norm_inv]
  have hnum : ‖f z - f I‖ ≤ 2 * M := by
    have h1 := hM z hz
    have h2 := hM I (by simp)
    calc ‖f z - f I‖ ≤ ‖f z‖ + ‖f I‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  have hden : R ^ 2 / 2 ≤ ‖1 + z ^ 2‖ := by
    have h1 : ‖z ^ 2‖ - ‖(1 : ℂ)‖ ≤ ‖1 + z ^ 2‖ := by
      have := norm_sub_norm_le (z ^ 2) (-1)
      simpa [sub_neg_eq_add, add_comm] using this
    rw [norm_pow, norm_one] at h1
    have h2 : R ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hzR 2
    nlinarith
  have hR2 : 0 < R ^ 2 / 2 := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM I (by simp))
  calc ‖1 + z ^ 2‖⁻¹ * ‖f z - f I‖ ≤ (R ^ 2 / 2)⁻¹ * (2 * M) := by
        apply mul_le_mul (inv_anti₀ hR2 hden) hnum (norm_nonneg _)
        exact inv_nonneg.mpr hR2.le
    _ = 4 * M / R ^ 2 := by field_simp; ring

/-- The real-axis integrand is integrable. -/
theorem integrable_poissonAux_real (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z) {M : ℝ}
    (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) :
    Integrable (fun x : ℝ => poissonAux f (x : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => poissonAux f (x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_poissonAux hf (z := (x : ℂ)) (by simp)).comp
      Complex.continuous_ofReal.continuousAt
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * M))
    hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hxI : (x : ℂ) ≠ I := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [poissonAux_eq (by simp) hxI, norm_mul, norm_inv]
  have h1 : ‖(1 : ℂ) + (x : ℂ) ^ 2‖ = 1 + x ^ 2 := by
    rw [show (1 : ℂ) + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h1]
  have hnum : ‖f x - f I‖ ≤ 2 * M := by
    have h1 := hM x (by simp)
    have h2 := hM I (by simp)
    calc ‖f x - f I‖ ≤ ‖f x‖ + ‖f I‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (by positivity))

/-- The real-axis integral of `poissonAux f` over `[-R, R]` is `O(M/R)`. -/
theorem norm_intervalIntegral_poissonAux_le (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z)
    {M : ℝ} (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) {R : ℝ} (hR : 2 ≤ R) :
    ‖∫ x in (-R)..R, poissonAux f (x : ℂ)‖ ≤ 16 * M / R := by
  have hR0 : 0 ≤ R := by linarith
  have hc : ContinuousOn (poissonAux f)
      (uIcc (⟨-R, 0⟩ : ℂ).re (⟨R, R⟩ : ℂ).re ×ℂ uIcc (⟨-R, 0⟩ : ℂ).im (⟨R, R⟩ : ℂ).im) := by
    intro z hz
    rw [mem_reProdIm] at hz
    have him : 0 ≤ z.im := by
      have := hz.2
      simp only [uIcc_of_le hR0] at this
      exact this.1
    exact (continuousAt_poissonAux hf him).continuousWithinAt
  have hd : DifferentiableOn ℂ (poissonAux f)
      (Ioo (min (⟨-R, 0⟩ : ℂ).re (⟨R, R⟩ : ℂ).re) (max (⟨-R, 0⟩ : ℂ).re (⟨R, R⟩ : ℂ).re) ×ℂ
        Ioo (min (⟨-R, 0⟩ : ℂ).im (⟨R, R⟩ : ℂ).im) (max (⟨-R, 0⟩ : ℂ).im (⟨R, R⟩ : ℂ).im)) := by
    refine (differentiableOn_poissonAux hf).mono fun z hz => ?_
    rw [mem_reProdIm] at hz
    have := hz.2
    simp only [min_eq_left hR0] at this
    exact this.1
  have h := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (poissonAux f) ⟨-R, 0⟩ ⟨R, R⟩ hc hd
  simp only [ofReal_zero, zero_mul, add_zero] at h
  set B := ∫ x in (-R)..R, poissonAux f (x : ℂ)
  set T := ∫ x in (-R)..R, poissonAux f ((x : ℂ) + (R : ℂ) * I)
  set S1 := ∫ y in (0 : ℝ)..R, poissonAux f ((R : ℂ) + (y : ℂ) * I)
  set S2 := ∫ y in (0 : ℝ)..R, poissonAux f ((-R : ℝ) + (y : ℂ) * I)
  have hB : B = T - I • S1 + I • S2 := by
    linear_combination h
  have hb : 4 * M / R ^ 2 = 4 * M / R ^ 2 := rfl
  have hT : ‖T‖ ≤ 4 * M / R ^ 2 * |R - -R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    refine norm_poissonAux_le hM hR (by simp [hR0]) ?_
    have := abs_im_le_norm ((x : ℂ) + (R : ℂ) * I)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add] at this
    rwa [abs_of_nonneg hR0] at this
  have hS1 : ‖S1‖ ≤ 4 * M / R ^ 2 * |R - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [uIoc_of_le hR0] at hy
    refine norm_poissonAux_le hM hR (by simp [hy.1.le]) ?_
    have := abs_re_le_norm ((R : ℂ) + (y : ℂ) * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_zero, add_zero] at this
    rwa [abs_of_nonneg hR0] at this
  have hS2 : ‖S2‖ ≤ 4 * M / R ^ 2 * |R - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [uIoc_of_le hR0] at hy
    refine norm_poissonAux_le hM hR (by simp [hy.1.le]) ?_
    have := abs_re_le_norm (((-R : ℝ) : ℂ) + (y : ℂ) * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_self, add_zero, abs_neg] at this
    rwa [abs_of_nonneg hR0] at this
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM I (by simp))
  have e1 : |R - -R| = 2 * R := by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; ring
  have e2 : |R - 0| = R := by rw [sub_zero, abs_of_nonneg hR0]
  rw [e1] at hT
  rw [e2] at hS1 hS2
  calc ‖B‖ = ‖T - I • S1 + I • S2‖ := by rw [hB]
    _ ≤ ‖T‖ + ‖S1‖ + ‖S2‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
        · rw [norm_smul, norm_I, one_mul]
        · rw [norm_smul, norm_I, one_mul]
    _ ≤ 4 * M / R ^ 2 * (2 * R) + 4 * M / R ^ 2 * R + 4 * M / R ^ 2 * R := by linarith
    _ = 16 * M / R := by field_simp; ring

/-- The real-axis integral of `poissonAux f` vanishes. -/
theorem integral_poissonAux_eq_zero (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z)
    {M : ℝ} (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) :
    ∫ x : ℝ, poissonAux f (x : ℂ) = 0 := by
  have hlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonAux f (x : ℂ)) atTop
      (𝓝 (∫ x : ℝ, poissonAux f (x : ℂ))) :=
    intervalIntegral_tendsto_integral (integrable_poissonAux_real hf hM) tendsto_neg_atTop_atBot
      tendsto_id
  have hzero : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonAux f (x : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 16 * M)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact norm_intervalIntegral_poissonAux_le hf hM hR
  exact tendsto_nhds_unique hlim hzero

end

/-- Poisson representation at `ζ = i`. For `f : ℂ → ℂ` complex-differentiable at every
point of the closed upper half-plane and bounded there by `M`, the function
`t ↦ (1 + t²)⁻¹ f(t)` is Lebesgue integrable on `ℝ` and
`∫_ℝ (1 + t²)⁻¹ f(t) dt = π f(i)` (the Poisson kernel of the upper half-plane at `i` is
`1/(π(1+t²))`). -/
theorem poisson_upperHalfPlane {f : ℂ → ℂ} {M : ℝ}
    (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z) (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) :
    Integrable (fun t : ℝ => ((1 + t ^ 2)⁻¹ : ℝ) • f t) ∧
      ∫ t : ℝ, ((1 + t ^ 2)⁻¹ : ℝ) • f t = (Real.pi : ℂ) * f I := by
  have hreal : ∀ x : ℝ, poissonAux f (x : ℂ) =
      ((1 + x ^ 2)⁻¹ : ℝ) • f x - ((1 + x ^ 2)⁻¹ : ℝ) • f I := by
    intro x
    have hxI : (x : ℂ) ≠ I := by
      intro h
      have := congrArg Complex.im h
      simp at this
    rw [poissonAux_eq (by simp) hxI, ← smul_sub, Complex.real_smul]
    push_cast
    ring
  have hint2 : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹ : ℝ) • f I) :=
    integrable_inv_one_add_sq.smul_const _
  have hint1 : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹ : ℝ) • f x) := by
    have h := (integrable_poissonAux_real hf hM).add hint2
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, hreal x, sub_add_cancel]
  refine ⟨hint1, ?_⟩
  have h0 := integral_poissonAux_eq_zero hf hM
  simp_rw [hreal] at h0
  rw [integral_sub hint1 hint2, integral_smul_const, integral_univ_inv_one_add_sq,
    sub_eq_zero] at h0
  rw [h0, Complex.real_smul]

/-- Imaginary-part form of `poisson_upperHalfPlane`:
`∫_ℝ (1 + t²)⁻¹ Im f(t) dt = π Im f(i)`, with integrability. -/
theorem poisson_upperHalfPlane_im {f : ℂ → ℂ} {M : ℝ}
    (hf : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ f z) (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M) :
    Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ * (f t).im) ∧
      ∫ t : ℝ, (1 + t ^ 2)⁻¹ * (f t).im = Real.pi * (f I).im := by
  obtain ⟨hint, heq⟩ := poisson_upperHalfPlane hf hM
  have hfun : (fun t : ℝ => (1 + t ^ 2)⁻¹ * (f t).im) =
      fun t : ℝ => RCLike.im (((1 + t ^ 2)⁻¹ : ℝ) • f t) := by
    funext t
    simp only [RCLike.im_to_complex, Complex.real_smul, Complex.im_ofReal_mul]
  rw [hfun]
  refine ⟨hint.im, ?_⟩
  rw [integral_im hint, heq]
  simp

end BlockBand.Wegner
