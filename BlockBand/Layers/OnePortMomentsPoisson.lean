module

public import Mathlib.Analysis.Complex.MeanValue
public import BlockBand.Layers.LayerMeasurability

/-!
# A Poisson (mean-value) bound for matrix resolvents along a dissipative half-plane

The analytic step of the passive extension in the passive-bounds lemma: for fixed invertible `B`,
`F(ζ) = (A - E - X_h + ζY - z⁻¹BB*)⁻¹` is analytic and bounded on the closed upper half-plane,
and its value at `ζ = i` is controlled by a Poisson average over the real line.

Setting: a finite index type `n`; matrices over `ℂ` with the `ℓ²` operator norm
(`Matrix.Norms.L2Operator`); a deterministic affine pencil `ζ ↦ T₀ + ζ P`. Everything here is
deterministic.

## Main declarations

* `opmCayley w = i(1+w)/(1-w)`, the Cayley map of the unit disc onto the upper half-plane
  (`opmCayley 0 = i`; `Im ≥ 0` on the closed disc, `Im = 0` on the unit circle; Lean's
  `x / 0 = 0` sends `w = 1` to `0`).
* `opm_poisson_circleAverage`: if `T₀ + ζP` is invertible with `‖(T₀ + ζP)⁻¹‖ ≤ K` for every
  `Im ζ ≥ 0`, then `‖(T₀ + iP)⁻¹‖ ≤ 2 · circleAverage (w ↦ ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1`
  (the average is over real points `ζ = opmCayley w` of the boundary line).
* `opmAngle = (2π)⁻¹ dθ` on `(0, 2π]` (a probability measure) and `opm_poisson_lintegral`, the same
  bound as a lower Lebesgue integral over `opmAngle`, the form used with Tonelli.

## Proof (instead of subharmonicity of `‖F‖^p`)

`H(w) = ((1-w)/2) F(opmCayley w)`, `F(ζ) = (T₀ + ζP)⁻¹`, is holomorphic on the open unit disc and
continuous on the closed disc: at `w = 1` the factor `1 - w` kills the bounded `F`
(`‖H(w)‖ ≤ |1-w| K/2`). The mean value property (`circleAverage_of_differentiable_on_off_countable`)
gives `F(i)/2 = H(0) = circleAverage H 0 1`, and `|1-w| ≤ 2` on the circle. The multiplier `(1-w)/2`
replaces a Phragmén–Lindelöf/Poisson argument at the boundary point `∞` and costs the factor `2`.
The Poisson average of `‖F‖^p` then follows by Jensen in `OnePortMoments`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory Matrix Metric Filter Topology Set Real
open scoped Matrix.Norms.L2Operator ENNReal Real

/-!
## 1. The Cayley map
-/

/-- The Cayley map `w ↦ i(1+w)/(1-w)` of the unit disc onto the upper half-plane. -/
def opmCayley (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem opmCayley_zero : opmCayley 0 = Complex.I := by simp [opmCayley]

theorem opmCayley_im (w : ℂ) :
    (opmCayley w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  simp only [opmCayley, Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
    Complex.sub_im]
  rw [Complex.normSq_apply w]
  ring

/-- `Im (opmCayley w) ≥ 0` on the closed unit disc. -/
theorem opmCayley_im_nonneg {w : ℂ} (hw : ‖w‖ ≤ 1) : 0 ≤ (opmCayley w).im := by
  rw [opmCayley_im]
  refine div_nonneg ?_ (Complex.normSq_nonneg _)
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg w]

/-- `opmCayley w` is real on the unit circle. -/
theorem opmCayley_im_eq_zero {w : ℂ} (hw : ‖w‖ = 1) : (opmCayley w).im = 0 := by
  rw [opmCayley_im, Complex.normSq_eq_norm_sq, hw]
  simp

theorem measurable_opmCayley : Measurable opmCayley := by
  unfold opmCayley
  fun_prop

/-!
## 2. The mean-value bound
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `w ↦ ‖(T₀ + opmCayley w • P)⁻¹‖` is measurable. -/
theorem opm_measurable_norm_inv_cayley (T₀ P : Matrix n n ℂ) :
    Measurable (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) :=
  continuous_norm.measurable.comp
    (measurable_matrix_inv.comp (measurable_const.add (measurable_opmCayley.smul_const P)))

/-- **Mean-value (Poisson) bound for an affine resolvent pencil.** If `T₀ + ζP` is invertible
with `‖(T₀ + ζP)⁻¹‖ ≤ K` for every `ζ` with `Im ζ ≥ 0` (closed upper half-plane), then
`w ↦ ‖(T₀ + opmCayley w • P)⁻¹‖` is circle integrable on the unit circle and
`‖(T₀ + iP)⁻¹‖ ≤ 2 · circleAverage (fun w ↦ ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1`.
On the unit circle `opmCayley w` is real (`opmCayley_im_eq_zero`), so the right side averages the
resolvent norm over real points of the pencil only. Deterministic; `‖·‖` is the `ℓ²` operator
norm. -/
theorem opm_poisson_circleAverage (T₀ P : Matrix n n ℂ) {K : ℝ}
    (hU : ∀ ζ : ℂ, 0 ≤ ζ.im → IsUnit (T₀ + ζ • P).det)
    (hK : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖(T₀ + ζ • P)⁻¹‖ ≤ K) :
    CircleIntegrable (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1 ∧
      ‖(T₀ + Complex.I • P)⁻¹‖ ≤
        2 * circleAverage (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1 := by
  set F : ℂ → Matrix n n ℂ := fun ζ => (T₀ + ζ • P)⁻¹ with hF
  set H : ℂ → Matrix n n ℂ := fun w => ((1 - w) / 2) • F (opmCayley w) with hH
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (le_of_eq Complex.zero_im.symm))
  have hunit : ∀ w : ℂ, ‖w‖ ≤ 1 → IsUnit (T₀ + opmCayley w • P) := fun w hw =>
    (isUnit_iff_isUnit_det _).mpr (hU _ (opmCayley_im_nonneg hw))
  have hHr : H = fun w => ((1 - w) / 2) • Ring.inverse (T₀ + opmCayley w • P) := by
    funext w
    simp only [hH, hF, nonsing_inv_eq_ringInverse]
  have hdiff : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → DifferentiableAt ℂ H w := by
    intro w hw h1
    have hw1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hc : DifferentiableAt ℂ opmCayley w := by
      unfold opmCayley
      exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
        ((differentiableAt_const _).sub differentiableAt_id) hw1
    have hT : DifferentiableAt ℂ (fun w => T₀ + opmCayley w • P) w :=
      (hc.smul_const P).const_add T₀
    have hI : DifferentiableAt ℂ (fun w => Ring.inverse (T₀ + opmCayley w • P)) w :=
      hT.inverse (hunit w hw)
    rw [hHr]
    exact (((differentiableAt_const _).sub differentiableAt_id).div_const 2).smul hI
  have hHle : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖H w‖ ≤ ‖1 - w‖ / 2 * ‖F (opmCayley w)‖ := by
    intro w _
    simp only [hH, norm_smul, norm_div, Complex.norm_ofNat, le_refl]
  have hcont : ContinuousOn H (closedBall 0 |1|) := by
    rw [abs_one]
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    by_cases h1 : w = 1
    · subst h1
      have hH1 : H 1 = 0 := by simp [hH]
      rw [ContinuousWithinAt, hH1]
      refine squeeze_zero_norm' (a := fun w : ℂ => ‖1 - w‖ / 2 * K) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with w hw'
        rw [mem_closedBall, dist_zero_right] at hw'
        refine (hHle w hw').trans ?_
        exact mul_le_mul_of_nonneg_left (hK _ (opmCayley_im_nonneg hw')) (by positivity)
      · have hc : Continuous (fun w : ℂ => ‖1 - w‖ / 2 * K) :=
          ((continuous_const.sub continuous_id).norm.div_const 2).mul continuous_const
        have h := hc.tendsto 1
        simp only [sub_self, norm_zero, zero_div, zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
    · exact (hdiff w hw h1).continuousAt.continuousWithinAt
  have hmv : circleAverage H 0 1 = H 0 := by
    refine circleAverage_of_differentiable_on_off_countable Set.countable_empty hcont ?_
    intro w hw
    rw [sdiff_empty, abs_one, mem_ball, dist_zero_right] at hw
    refine hdiff w hw.le ?_
    rintro rfl
    simp at hw
  have hH0 : H 0 = ((1 : ℂ) / 2) • F Complex.I := by
    simp only [hH, sub_zero, opmCayley_zero]
  have hint2 : CircleIntegrable (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1 := by
    unfold CircleIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
    refine Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne
      ((opm_measurable_norm_inv_cayley T₀ P).comp
        (continuous_circleMap 0 1).measurable).aestronglyMeasurable ?_
    refine ae_of_all _ fun θ => ?_
    simp only [norm_norm]
    refine hK _ (le_of_eq (opmCayley_im_eq_zero ?_).symm)
    simp [norm_circleMap_zero]
  have hint1 : CircleIntegrable (fun w : ℂ => ‖H w‖) 0 1 :=
    ContinuousOn.circleIntegrable zero_le_one
      ((hcont.mono (by rw [abs_one]; exact sphere_subset_closedBall)).norm)
  refine ⟨hint2, ?_⟩
  have hmono : circleAverage (fun w : ℂ => ‖H w‖) 0 1 ≤
      circleAverage (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1 := by
    refine circleAverage_mono hint1 hint2 fun w hw => ?_
    rw [abs_one, mem_sphere, dist_zero_right] at hw
    refine (hHle w hw.le).trans ?_
    have h2 : ‖1 - w‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hw, norm_one]; norm_num)
    have := norm_nonneg (F (opmCayley w))
    calc ‖1 - w‖ / 2 * ‖F (opmCayley w)‖ ≤ 1 * ‖F (opmCayley w)‖ := by gcongr; linarith
      _ = ‖(T₀ + opmCayley w • P)⁻¹‖ := one_mul _
  have hnorm : ‖F Complex.I‖ = 2 * ‖H 0‖ := by
    rw [hH0, norm_smul, norm_div, norm_one, Complex.norm_ofNat]
    ring
  calc ‖(T₀ + Complex.I • P)⁻¹‖ = 2 * ‖H 0‖ := hnorm
    _ = 2 * ‖circleAverage H 0 1‖ := by rw [hmv]
    _ ≤ 2 * circleAverage (fun w : ℂ => ‖H w‖) 0 1 := by
        gcongr; exact norm_circleAverage_le_circleAverage_norm
    _ ≤ 2 * circleAverage (fun w : ℂ => ‖(T₀ + opmCayley w • P)⁻¹‖) 0 1 := by gcongr

/-!
## 3. The lower-integral form over the normalized angle measure
-/

/-- The normalized angle measure `(2π)⁻¹ dθ` on `(0, 2π]`. -/
def opmAngle : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance opm_isProbabilityMeasure_opmAngle : IsProbabilityMeasure opmAngle := by
  constructor
  rw [opmAngle, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ Real.two_pi_pos.ne',
    ENNReal.ofReal_one]

/-- **Poisson bound, lower-integral form.** Under the hypotheses of `opm_poisson_circleAverage`,
`‖(T₀ + iP)⁻¹‖ ≤ 2 ∫ ‖(T₀ + opmCayley(e^{iθ}) • P)⁻¹‖ dopmAngle(θ)` (as extended reals), where
`opmCayley (circleMap 0 1 θ)` is real for every `θ`. Deterministic. -/
theorem opm_poisson_lintegral (T₀ P : Matrix n n ℂ) {K : ℝ}
    (hU : ∀ ζ : ℂ, 0 ≤ ζ.im → IsUnit (T₀ + ζ • P).det)
    (hK : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖(T₀ + ζ • P)⁻¹‖ ≤ K) :
    ENNReal.ofReal ‖(T₀ + Complex.I • P)⁻¹‖ ≤
      2 * ∫⁻ θ, ENNReal.ofReal ‖(T₀ + opmCayley (circleMap 0 1 θ) • P)⁻¹‖ ∂opmAngle := by
  obtain ⟨hint, hle⟩ := opm_poisson_circleAverage T₀ P hU hK
  set f : ℝ → ℝ := fun θ => ‖(T₀ + opmCayley (circleMap 0 1 θ) • P)⁻¹‖ with hf
  have hfi : IntegrableOn f (Ioc 0 (2 * π)) volume := by
    have := hint
    unfold CircleIntegrable at this
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le] at this
  rw [circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le, smul_eq_mul] at hle
  have hlint : ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), f θ) =
      ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (f θ) :=
    ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun θ => norm_nonneg _)
  calc ENNReal.ofReal ‖(T₀ + Complex.I • P)⁻¹‖
      ≤ ENNReal.ofReal (2 * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), f θ)) :=
        ENNReal.ofReal_le_ofReal hle
    _ = 2 * (ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (f θ)) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_mul (by positivity), hlint]
    _ = 2 * ∫⁻ θ, ENNReal.ofReal (f θ) ∂opmAngle := by
        rw [opmAngle, lintegral_smul_measure, smul_eq_mul]

end BlockBand.Layers
