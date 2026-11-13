module

public import BlockBand.SourceProcess.RawTag.StepIneq
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The one-step moment inequality integrated over a fresh layer

`lintegral_fresh_step`: for a centred integrable `d` under a probability measure and `W ≥ 1`,
`E|u + d|^{2n} ≤ (1 + K/W)|u|^{2n} + K W^{n-1} E|d|^{2n}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory
open scoped ENNReal

/-- **One fresh step**: `E|u+d|^{2n} ≤ (1+K/W)|u|^{2n} + KW^{n-1}E|d|^{2n}` for centred `d`. -/
theorem lintegral_fresh_step {F : Type*} [MeasurableSpace F] {ν : Measure F}
    [IsProbabilityMeasure ν] (u : ℂ) {d : F → ℂ} (hd : Integrable d ν) (hd0 : ∫ f, d f ∂ν = 0)
    {m : ℕ} (hm : 1 ≤ m) {W : ℝ} (hW : 1 ≤ W) :
    ∫⁻ f, ENNReal.ofReal ((‖u + d f‖ ^ 2) ^ (2 * m)) ∂ν ≤
      ENNReal.ofReal ((1 + stepK (2 * m) / W) * (‖u‖ ^ 2) ^ (2 * m)) +
        ENNReal.ofReal (stepK (2 * m) * W ^ (2 * m - 1)) *
          ∫⁻ f, ENNReal.ofReal ((‖d f‖ ^ 2) ^ (2 * m)) ∂ν := by
  set n := 2 * m
  set K := stepK n
  set J := ∫⁻ f, ENNReal.ofReal ((‖d f‖ ^ 2) ^ n) ∂ν
  have hK : 0 < K := stepK_pos n
  have hW0 : 0 < W := by linarith
  have hB : 0 < K * W ^ (n - 1) := by positivity
  by_cases hJ : J = ⊤
  · rw [hJ, ENNReal.mul_top (by simpa using hB), add_top]; exact le_top
  set h : F → ℝ := fun f => (‖d f‖ ^ 2) ^ n
  have hhm : AEStronglyMeasurable h ν := (hd.aestronglyMeasurable.norm.pow 2).pow n
  have hh0 : ∀ f, 0 ≤ h f := fun f => by positivity
  have hhi : Integrable h ν := by
    refine ⟨hhm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hh0)]
    exact lt_top_iff_ne_top.mpr hJ
  set t := ‖u‖ ^ 2
  set c : ℝ := (n : ℕ) * t ^ (n - 1)
  set g : F → ℝ := fun f => (1 + K / W) * t ^ n + c * (2 * ((starRingEnd ℂ) u * d f).re) +
    K * W ^ (n - 1) * h f
  have hpt : ∀ f, (‖u + d f‖ ^ 2) ^ n ≤ g f := by
    intro f
    have := step_pointwise u (d f) hm hW
    simp only [g, h, c, t, n, K] at this ⊢
    have e : stepK (2 * m) * ((‖u‖ ^ 2) ^ (2 * m) / W + W ^ (2 * m - 1) * (‖d f‖ ^ 2) ^ (2 * m)) =
        stepK (2 * m) / W * (‖u‖ ^ 2) ^ (2 * m) +
          stepK (2 * m) * W ^ (2 * m - 1) * (‖d f‖ ^ 2) ^ (2 * m) := by ring
    linarith
  have hre : Integrable (fun f => ((starRingEnd ℂ) u * d f).re) ν :=
    (hd.const_mul ((starRingEnd ℂ) u)).re
  have hgi : Integrable g ν :=
    ((integrable_const _).add (hre.const_mul _ |>.const_mul _)).add (hhi.const_mul _)
  have hg0 : ∀ f, 0 ≤ g f := fun f => (by positivity : (0 : ℝ) ≤ (‖u + d f‖ ^ 2) ^ n).trans
    (hpt f)
  have hint : ∫ f, g f ∂ν = (1 + K / W) * t ^ n + K * W ^ (n - 1) * ∫ f, h f ∂ν := by
    have hre0 : ∫ f, ((starRingEnd ℂ) u * d f).re ∂ν = 0 := by
      have e := Complex.reCLM.integral_comp_comm (hd.const_mul ((starRingEnd ℂ) u))
      simp only [Complex.reCLM_apply] at e
      rw [e, integral_const_mul, hd0, mul_zero, Complex.zero_re]
    have i2 : Integrable (fun f => c * (2 * ((starRingEnd ℂ) u * d f).re)) ν :=
      (hre.const_mul _).const_mul _
    have i1 : Integrable (fun f => (1 + K / W) * t ^ n +
        c * (2 * ((starRingEnd ℂ) u * d f).re)) ν := (integrable_const _).add i2
    have i3 : Integrable (fun f => K * W ^ (n - 1) * h f) ν := hhi.const_mul _
    simp only [g]
    rw [integral_add i1 i3, integral_add (integrable_const _) i2, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul, hre0]
    simp
  calc ∫⁻ f, ENNReal.ofReal ((‖u + d f‖ ^ 2) ^ n) ∂ν ≤ ∫⁻ f, ENNReal.ofReal (g f) ∂ν :=
        lintegral_mono fun f => ENNReal.ofReal_le_ofReal (hpt f)
    _ = ENNReal.ofReal (∫ f, g f ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)).symm
    _ = ENNReal.ofReal ((1 + K / W) * t ^ n) +
        ENNReal.ofReal (K * W ^ (n - 1)) * ENNReal.ofReal (∫ f, h f ∂ν) := by
        rw [hint, ENNReal.ofReal_add (by positivity)
          (mul_nonneg hB.le (integral_nonneg hh0)), ENNReal.ofReal_mul hB.le]
    _ = _ := by
        rw [ofReal_integral_eq_lintegral_ofReal hhi (Filter.Eventually.of_forall hh0)]

end BlockBand.SourceProcess.RawTag
