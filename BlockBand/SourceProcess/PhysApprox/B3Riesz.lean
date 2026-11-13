module

public import BlockBand.SourceProcess.Closing.PhaseAvg
public import Mathlib.Analysis.Complex.MeanValue

/-!
# M. Riesz at `p = 4` under the uniform phase

For `f` complex differentiable on the closed unit disc with `f(0) = 0`, write `F(θ) = f(e^{iθ})`,
`u = Re F`, `v = Im F`. Then `f⁴` is differentiable on the closed disc, so by the mean value
property (`DiffContOnCl.circleAverage`) `E_θ F⁴ = f(0)⁴ = 0`, and in particular
`E_θ Re F⁴ = E_θ(u⁴ − 6u²v² + v⁴) = 0`. Pointwise
`(u² + v²)² = 48v⁴ + 2 Re F⁴ − (u² − 7v²)² ≤ 48v⁴ + 2 Re F⁴`, so
`E_θ|F|⁴ ≤ 48 E_θ v⁴`.

* `integral_phaseLaw_eq_circleAverage`: `E_θ g(e^{iθ})` is Mathlib's `circleAverage g 0 1`;
* `integral_phaseLaw_of_diffContOnCl`: the mean value property under `phaseLaw`;
* **`lintegral_phase_riesz_four`**: `E_θ|f|⁴ ≤ 48 E_θ|Im f|⁴`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory
open BlockBand.SourceProcess.Closing
open scoped ENNReal

theorem circleMap_zero_one_eq_phase (θ : ℝ) : circleMap 0 1 θ = phase θ := by
  simp [circleMap, phase]

/-- The uniform phase average is Mathlib's circle average on the unit circle. -/
theorem integral_phaseLaw_eq_circleAverage (g : ℂ → ℂ) :
    ∫ θ, g (phase θ) ∂phaseLaw = Real.circleAverage g 0 1 := by
  rw [Real.circleAverage_def, phaseLaw, integral_smul_measure, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [circleMap_zero_one_eq_phase]

/-- **The mean value property under `phaseLaw`.** -/
theorem integral_phaseLaw_of_diffContOnCl {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 1)) : ∫ θ, g (phase θ) ∂phaseLaw = g 0 := by
  have h1 : DiffContOnCl ℂ g (Metric.ball 0 |(1 : ℝ)|) := by rwa [abs_one]
  rw [integral_phaseLaw_eq_circleAverage]
  exact h1.circleAverage

theorem integrable_real_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g phaseLaw := by
  simpa using (integrable_of_continuous (Complex.continuous_ofReal.comp hg)).re

theorem re_pow_four (z : ℂ) : (z ^ 4).re = z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  ring

/-- The pointwise inequality `|z|⁴ ≤ 48 (Im z)⁴ + 2 Re z⁴`. -/
theorem norm_pow_four_le (z : ℂ) : ‖z‖ ^ 4 ≤ 48 * z.im ^ 4 + 2 * (z ^ 4).re := by
  have hn : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by
    rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn, re_pow_four]
  nlinarith [sq_nonneg (z.re ^ 2 - 7 * z.im ^ 2)]

/-- **M. Riesz at `p = 4` under `phaseLaw`**: for `f` complex differentiable on the closed unit
disc with `f(0) = 0`, `E_θ|f(e^{iθ})|⁴ ≤ 48 E_θ|Im f(e^{iθ})|⁴`. -/
theorem lintegral_phase_riesz_four {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 1)) (h0 : f 0 = 0) :
    ∫⁻ θ, ‖f (phase θ)‖ₑ ^ 4 ∂phaseLaw ≤ 48 * ∫⁻ θ, ‖(f (phase θ)).im‖ₑ ^ 4 ∂phaseLaw := by
  have hmem : ∀ θ, phase θ ∈ Metric.closedBall (0 : ℂ) 1 := fun θ => by
    rw [Metric.mem_closedBall, dist_zero_right, norm_phase]
  have hF : Continuous fun θ => f (phase θ) :=
    hf.continuousOn.comp_continuous continuous_phase hmem
  -- `E_θ F⁴ = 0` (mean value property for `f⁴`)
  have hdc : DiffContOnCl ℂ (fun z => f z ^ 4) (Metric.ball 0 1) :=
    (hf.pow 4).diffContOnCl_ball subset_rfl
  have hmean : ∫ θ, f (phase θ) ^ 4 ∂phaseLaw = 0 := by
    rw [integral_phaseLaw_of_diffContOnCl hdc, h0]
    norm_num
  have hre : ∫ θ, (f (phase θ) ^ 4).re ∂phaseLaw = 0 := by
    have h := integral_re (𝕜 := ℂ) (f := fun θ => f (phase θ) ^ 4)
      (integrable_of_continuous (hF.pow 4))
    simp only [RCLike.re_to_complex] at h
    rw [h, hmean, Complex.zero_re]
  have hA : Integrable (fun θ => ‖f (phase θ)‖ ^ 4) phaseLaw :=
    integrable_real_of_continuous (hF.norm.pow 4)
  have hB : Integrable (fun θ => (f (phase θ)).im ^ 4) phaseLaw :=
    integrable_real_of_continuous ((Complex.continuous_im.comp hF).pow 4)
  have hC : Integrable (fun θ => (f (phase θ) ^ 4).re) phaseLaw :=
    integrable_real_of_continuous (Complex.continuous_re.comp (hF.pow 4))
  have hint : ∫ θ, ‖f (phase θ)‖ ^ 4 ∂phaseLaw ≤ 48 * ∫ θ, (f (phase θ)).im ^ 4 ∂phaseLaw := by
    calc ∫ θ, ‖f (phase θ)‖ ^ 4 ∂phaseLaw ≤
          ∫ θ, (48 * (f (phase θ)).im ^ 4 + 2 * (f (phase θ) ^ 4).re) ∂phaseLaw :=
          integral_mono hA ((hB.const_mul 48).add (hC.const_mul 2))
            fun θ => norm_pow_four_le (f (phase θ))
      _ = 48 * ∫ θ, (f (phase θ)).im ^ 4 ∂phaseLaw := by
          rw [integral_add (hB.const_mul 48) (hC.const_mul 2), integral_const_mul,
            integral_const_mul, hre, mul_zero, add_zero]
  have e1 : ∫⁻ θ, ‖f (phase θ)‖ₑ ^ 4 ∂phaseLaw =
      ENNReal.ofReal (∫ θ, ‖f (phase θ)‖ ^ 4 ∂phaseLaw) := by
    rw [ofReal_integral_eq_lintegral_ofReal hA (ae_of_all _ fun θ => by positivity)]
    refine lintegral_congr fun θ => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have e2 : ∫⁻ θ, ‖(f (phase θ)).im‖ₑ ^ 4 ∂phaseLaw =
      ENNReal.ofReal (∫ θ, (f (phase θ)).im ^ 4 ∂phaseLaw) := by
    rw [ofReal_integral_eq_lintegral_ofReal hB (ae_of_all _ fun θ => by positivity)]
    refine lintegral_congr fun θ => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (by positivity)]
  rw [e1, e2]
  calc ENNReal.ofReal (∫ θ, ‖f (phase θ)‖ ^ 4 ∂phaseLaw) ≤
        ENNReal.ofReal (48 * ∫ θ, (f (phase θ)).im ^ 4 ∂phaseLaw) := ENNReal.ofReal_le_ofReal hint
    _ = 48 * ENNReal.ofReal (∫ θ, (f (phase θ)).im ^ 4 ∂phaseLaw) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

end BlockBand.SourceProcess.PhysApprox.B3
