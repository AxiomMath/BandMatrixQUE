module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbLaw

/-!
# The zero-entrance lemma: contour and centering tools

We collect the contour-integral and centering estimates used for the conditional fluctuation bound
of the zero-entrance lemma.

* `norm_le_circleAvg`: Cauchy's integral formula on a fixed circle bounds a holomorphic function
  at every point of a smaller concentric disc by its circle average,
  `|F(ζ)| ≤ ρ/(ρ - ρ₁) · (2π)⁻¹ ∫₀^{2π} |F(c₀ + ρ e^{iθ})| dθ` for `|ζ - c₀| ≤ ρ₁ < ρ`.
  This is what makes the conditional fluctuation bound uniform in the old input: the cavity
  argument of the next layer lies in a fixed compact region of the upper half-plane, and the
  supremum over that region of `|f_X - E f_X|` is dominated by one circle average.
* `exists_circle`: an explicit circle in the upper half-plane enclosing the compact region
  `{s ≤ Im ζ, |ζ| ≤ R}`.
* `eLpNorm_sub_integral_le_two_mul`: `‖g - E g‖_p ≤ 2 ‖g - c‖_p` on a probability space.
* `eLpNorm_const_prob`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Metric Complex
open scoped ENNReal NNReal Real

namespace ZeroEntranceProb

/-- **Cauchy bound on a fixed circle.** -/
theorem norm_le_circleAvg {F : ℂ → ℂ} {c₀ : ℂ} {ρ₁ ρ : ℝ} (h1 : ρ₁ < ρ)
    (hF : DifferentiableOn ℂ F (closedBall c₀ ρ)) {ζ : ℂ} (hζ : ‖ζ - c₀‖ ≤ ρ₁) :
    ‖F ζ‖ ≤ ρ / (ρ - ρ₁) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖F (circleMap c₀ ρ θ)‖) := by
  have hρ₁ : 0 ≤ ρ₁ := (norm_nonneg _).trans hζ
  have hρ : 0 < ρ := hρ₁.trans_lt h1
  have hgap : 0 < ρ - ρ₁ := by linarith
  have hw : ζ ∈ ball c₀ ρ := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hC := hF.circleIntegral_sub_inv_smul hw
  have hcont : Continuous (fun θ : ℝ => ‖F (circleMap c₀ ρ θ)‖) :=
    (hF.continuousOn.comp_continuous (continuous_circleMap c₀ ρ)
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere c₀ hρ.le θ))).norm
  have hbd : ‖∮ z in C(c₀, ρ), (z - ζ)⁻¹ • F z‖ ≤
      ∫ θ in (0 : ℝ)..2 * π, ρ / (ρ - ρ₁) * ‖F (circleMap c₀ ρ θ)‖ := by
    unfold circleIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
      (Filter.Eventually.of_forall fun θ _ => ?_) ((hcont.const_mul _).intervalIntegrable _ _)
    rw [norm_smul, norm_smul, CavityMeanProb.norm_deriv_circleMap hρ.le]
    have hd : ρ - ρ₁ ≤ ‖circleMap c₀ ρ θ - ζ‖ := by
      have h2 : ‖circleMap c₀ ρ θ - c₀‖ = ρ := by
        rw [← dist_eq_norm]; exact (circleMap_mem_sphere c₀ hρ.le θ)
      have := norm_sub_norm_le (circleMap c₀ ρ θ - c₀) (ζ - c₀)
      rw [h2, sub_sub_sub_cancel_right] at this
      linarith
    have hinv : ‖(circleMap c₀ ρ θ - ζ)⁻¹‖ ≤ 1 / (ρ - ρ₁) := by
      rw [norm_inv]; exact (inv_le_inv₀ (hgap.trans_le hd) hgap).mpr hd |>.trans_eq (one_div _).symm
    calc ρ * (‖(circleMap c₀ ρ θ - ζ)⁻¹‖ * ‖F (circleMap c₀ ρ θ)‖)
        ≤ ρ * (1 / (ρ - ρ₁) * ‖F (circleMap c₀ ρ θ)‖) := by gcongr
      _ = ρ / (ρ - ρ₁) * ‖F (circleMap c₀ ρ θ)‖ := by ring
  rw [intervalIntegral.integral_const_mul] at hbd
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
      Real.norm_of_nonneg Real.pi_pos.le]; ring
  have key : 2 * π * ‖F ζ‖ ≤ ρ / (ρ - ρ₁) * ∫ θ in (0 : ℝ)..2 * π, ‖F (circleMap c₀ ρ θ)‖ := by
    rw [hC, norm_smul, h2pi] at hbd; exact hbd
  have hpi : 0 < 2 * π := Real.two_pi_pos
  rw [← mul_assoc, mul_comm (ρ / (ρ - ρ₁)), mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpi]
  linarith

/-- An explicit circle enclosing `{s ≤ Im ζ, |ζ| ≤ R}` inside `{Im ≥ η'}`. -/
theorem exists_circle {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    ∃ (c₀ : ℂ) (ρ₁ ρ η' M' : ℝ), 0 ≤ ρ₁ ∧ ρ₁ < ρ ∧ 0 < η' ∧ η' ≤ s ∧ R ≤ M' ∧
      (∀ ζ : ℂ, s ≤ ζ.im → ‖ζ‖ ≤ R → ‖ζ - c₀‖ ≤ ρ₁) ∧
      (∀ w ∈ closedBall c₀ ρ, η' ≤ w.im ∧ ‖w‖ ≤ M') := by
  set Y : ℝ := R ^ 2 / s + s with hY
  have hR0 : 0 < R := hs.trans_le hsR
  have hRY : R ^ 2 / s ≥ R := by rw [ge_iff_le, le_div_iff₀ hs]; nlinarith
  have hYs : s ≤ Y := by have : 0 ≤ R ^ 2 / s := by positivity
                         linarith
  have hY0 : 0 < Y := hs.trans_le hYs
  have hρ₁ : 0 ≤ Y - s ^ 2 / (2 * Y) := by
    have : s ^ 2 / (2 * Y) ≤ Y := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨(Y : ℂ) * I, Y - s ^ 2 / (2 * Y), Y - s ^ 2 / (4 * Y), s ^ 2 / (4 * Y), 2 * Y,
    hρ₁, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · have : s ^ 2 / (4 * Y) < s ^ 2 / (2 * Y) :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
    linarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · linarith
  · intro ζ hζs hζR
    have hsq : ‖ζ - (Y : ℂ) * I‖ ^ 2 = ζ.re ^ 2 + (ζ.im - Y) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have hζsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hRR : ζ.re ^ 2 + ζ.im ^ 2 ≤ R ^ 2 := by
      rw [← hζsq]; exact pow_le_pow_left₀ (norm_nonneg _) hζR 2
    have hYdef : Y * s = R ^ 2 + s ^ 2 := by rw [hY]; field_simp
    have hlhs : ‖ζ - (Y : ℂ) * I‖ ^ 2 ≤ Y ^ 2 - s ^ 2 := by
      rw [hsq]; nlinarith
    have hrhs : Y ^ 2 - s ^ 2 ≤ (Y - s ^ 2 / (2 * Y)) ^ 2 := by
      have : (Y - s ^ 2 / (2 * Y)) ^ 2 = Y ^ 2 - s ^ 2 + (s ^ 2 / (2 * Y)) ^ 2 := by
        field_simp; ring
      rw [this]; nlinarith [sq_nonneg (s ^ 2 / (2 * Y))]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ₁ two_ne_zero).mp (hlhs.trans hrhs)
  · intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have him : |(w - (Y : ℂ) * I).im| ≤ ‖w - (Y : ℂ) * I‖ := Complex.abs_im_le_norm _
    have hsub : (w - (Y : ℂ) * I).im = w.im - Y := by simp
    rw [hsub, abs_le] at him
    constructor
    · linarith
    · have := norm_sub_norm_le w ((Y : ℂ) * I)
      have hYn : ‖(Y : ℂ) * I‖ = Y := by
        rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hY0.le, mul_one]
      have : s ^ 2 / (4 * Y) ≥ 0 := by positivity
      linarith

/-- The `L^p` norm of a constant on a probability space. -/
theorem eLpNorm_const_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p) (c : ℝ) :
    eLpNorm (fun _ : Ω => c) (ENNReal.ofReal p) μ = ENNReal.ofReal |c| := by
  rw [eLpNorm_const _ (by simpa using hp) (IsProbabilityMeasure.ne_zero μ), measure_univ,
    ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]

/-- `‖g - E g‖_p ≤ 2 ‖g - c‖_p` on a probability space (`p ≥ 1`). -/
theorem eLpNorm_sub_integral_le_two_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g : Ω → ℂ} (hg : Integrable g μ) {p : ℝ} (hp : 1 ≤ p) (c : ℂ) :
    eLpNorm (fun ω => g ω - ∫ ω', g ω' ∂μ) (ENNReal.ofReal p) μ ≤
      2 * eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ := by
  have hgc : Integrable (fun ω => g ω - c) μ := hg.sub (integrable_const c)
  have hint : ∫ ω', g ω' ∂μ - c = ∫ ω', (g ω' - c) ∂μ := by
    rw [integral_sub hg (integrable_const c), integral_const, probReal_univ, one_smul]
  have hsplit : (fun ω => g ω - ∫ ω', g ω' ∂μ) =
      (fun ω => g ω - c) - fun _ => ∫ ω', (g ω' - c) ∂μ := by
    funext ω; simp only [Pi.sub_apply]; rw [← hint]; ring
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  rw [hsplit]
  refine (eLpNorm_sub_le hp1).trans ?_
  have hc : eLpNorm (fun _ : Ω => ∫ ω', (g ω' - c) ∂μ) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ := by
    rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_of_exponent_le hp1
    exact hgc.aestronglyMeasurable
  calc eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ +
        eLpNorm (fun _ : Ω => ∫ ω', (g ω' - c) ∂μ) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ +
          eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ := by gcongr
    _ = 2 * eLpNorm (fun ω => g ω - c) (ENNReal.ofReal p) μ := by rw [two_mul]

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
