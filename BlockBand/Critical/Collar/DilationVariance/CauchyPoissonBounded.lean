module

public import BlockBand.Coarea.Native.BlockBand.Analysis.CauchyPoissonUpperHalfPlane
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Probability.Distributions.Cauchy

/-!
# Bounded Cauchy–Poisson formula on the closed upper half-plane

* `integral_standardCauchyWeight_smul_eq_circleParam` — the standard Cauchy density
  `1/(π(1+t²))` is normalized angular measure under `φ ↦ tan(φ/2 - π/2)`, for functions with
  values in any real Banach space.
* `integral_standardCauchyWeight_smul_eq_of_analyticAt` — for `F : ℂ → E` (`E` a complex
  Banach space) analytic at every point of the *closed* upper half-plane `{0 ≤ Im w}` and bounded
  there by `M`, `∫ t, (1/(π(1+t²))) • F t dt = F i`.
* `integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul` — the Mathlib law
  `ProbabilityTheory.cauchyMeasure 0 1` (location `0`, scale `1`) integrates against the same
  density.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal

namespace BlockBand.Critical.Collar

open CoareaNative.BlockBand (standardCauchyWeight diskToUpperHalfPlane radialRadius
  im_diskToUpperHalfPlane im_diskToUpperHalfPlane_pos diskToUpperHalfPlane_exp_mul_I)

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tangent change of variables `(-π/2, π/2) → ℝ`, for an arbitrary (not necessarily
integrable) `f : ℝ → E`; both sides are Mathlib's totalized Bochner integrals. -/
theorem integral_eq_integral_tan_jacobian_smul (f : ℝ → E) :
    (∫ t : ℝ, f t) =
      ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2),
        (1 + Real.tan θ ^ 2) • f (Real.tan θ) := by
  have hderiv : ∀ θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivWithinAt Real.tan (1 / Real.cos θ ^ 2)
        (Ioo (-(Real.pi / 2)) (Real.pi / 2)) θ := by
    intro θ hθ
    exact (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo hθ).ne').hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv Real.injOn_tan f
  rw [Real.image_tan_Ioo] at h
  simp only [Measure.restrict_univ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  dsimp only
  rw [abs_of_pos (div_pos zero_lt_one (sq_pos_of_pos hcos))]
  congr 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The standard Cauchy density `1/(π(1+t²))` is the pushforward of `π⁻¹` times Lebesgue
measure on `(-π/2, π/2)` under `tan`; vector-valued, no integrability hypothesis. -/
theorem integral_standardCauchyWeight_smul_eq_tan (f : ℝ → E) :
    (∫ t : ℝ, standardCauchyWeight t • f t) =
      Real.pi⁻¹ • ∫ θ in Ioo (-(Real.pi / 2)) (Real.pi / 2), f (Real.tan θ) := by
  rw [integral_eq_integral_tan_jacobian_smul]
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _hθ
  dsimp only
  rw [smul_smul]
  congr 1
  unfold standardCauchyWeight
  have : (0 : ℝ) < 1 + Real.tan θ ^ 2 := by positivity
  field_simp

/-- Full-circle parameterization of the standard Cauchy law: `φ ↦ tan(φ/2 - π/2)` on
`[0, 2π]`, normalized by `(2π)⁻¹`; vector-valued, no integrability hypothesis. -/
theorem integral_standardCauchyWeight_smul_eq_circleParam (f : ℝ → E) :
    (∫ t : ℝ, standardCauchyWeight t • f t) =
      (2 * Real.pi)⁻¹ •
        ∫ φ in (0 : ℝ)..(2 * Real.pi), f (Real.tan (φ / 2 - Real.pi / 2)) := by
  rw [integral_standardCauchyWeight_smul_eq_tan]
  have hsub := intervalIntegral.integral_comp_mul_sub
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (c := (1 / 2 : ℝ)) (fun θ : ℝ => f (Real.tan θ))
    (by norm_num) (Real.pi / 2)
  simp only [one_div, inv_inv] at hsub
  rw [show (2 : ℝ)⁻¹ * 0 - Real.pi / 2 = -(Real.pi / 2) by ring,
    show (2 : ℝ)⁻¹ * (2 * Real.pi) - Real.pi / 2 = Real.pi / 2 by ring]
    at hsub
  have hshape : (fun φ : ℝ => f (Real.tan (φ / 2 - Real.pi / 2))) =
      (fun φ : ℝ => f (Real.tan ((2 : ℝ)⁻¹ * φ - Real.pi / 2))) := by
    funext φ
    congr 2
    ring
  rw [hshape, hsub, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    MeasureTheory.integral_Ioc_eq_integral_Ioo, smul_smul]
  congr 1
  field_simp

end ChangeOfVariables

section Poisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem analyticAt_diskToUpperHalfPlane' {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ diskToUpperHalfPlane w := by
  unfold diskToUpperHalfPlane
  fun_prop (discharger := exact sub_ne_zero.mpr hw.symm)

private lemma radialRadius_nonneg' (n : ℕ) : 0 ≤ radialRadius n := by
  unfold radialRadius
  positivity

private lemma radialRadius_lt_one' (n : ℕ) : radialRadius n < 1 := by
  unfold radialRadius
  rw [div_lt_one (by positivity)]
  norm_num

private lemma tendsto_radialRadius' :
    Tendsto radialRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1)
  exact tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1

private lemma norm_radial_circle_lt_one' (n : ℕ) (φ : ℝ) :
    ‖(radialRadius n : ℂ) * Complex.exp (φ * Complex.I)‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    mul_one, Real.norm_of_nonneg (radialRadius_nonneg' n)]
  exact radialRadius_lt_one' n

private lemma ne_one_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  rintro rfl
  simp at hw

/-- Mean value on every circle of radius `r < 1` for the Cayley pullback of a function
analytic on the closed upper half-plane. -/
theorem circleAverage_comp_diskToUpperHalfPlane
    (F : ℂ → E) (hF : ∀ w : ℂ, 0 ≤ w.im → AnalyticAt ℂ F w)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun w => F (diskToUpperHalfPlane w)) 0 r = F Complex.I := by
  have hdiff : DifferentiableOn ℂ (fun w => F (diskToUpperHalfPlane w))
      (closure (ball (0 : ℂ) |r|)) := by
    intro w hw
    have hw' : w ∈ closedBall (0 : ℂ) |r| := closure_ball_subset_closedBall hw
    have hwr : ‖w‖ < 1 := by
      rw [mem_closedBall, dist_zero_right, abs_of_nonneg hr0] at hw'
      exact lt_of_le_of_lt hw' hr1
    exact ((hF _ (im_diskToUpperHalfPlane_pos hwr).le).comp
      (analyticAt_diskToUpperHalfPlane' (ne_one_of_norm_lt_one hwr))).differentiableAt
      |>.differentiableWithinAt
  rw [hdiff.diffContOnCl.circleAverage]
  simp

omit [CompleteSpace E] in
/-- Radial boundary convergence of the circle integrals, dominated by the bound `M`. -/
theorem tendsto_radial_integral_comp_diskToUpperHalfPlane
    (F : ℂ → E) (hF : ∀ w : ℂ, 0 ≤ w.im → AnalyticAt ℂ F w)
    (M : ℝ) (hM : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ M) :
    Tendsto
      (fun n : ℕ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        F (diskToUpperHalfPlane ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I))))
      atTop
      (𝓝 (∫ φ in (0 : ℝ)..(2 * Real.pi), F (Real.tan (φ / 2 - Real.pi / 2) : ℂ))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => M)
  · filter_upwards with n
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro φ
    have hw := norm_radial_circle_lt_one' n φ
    have hc : Continuous (fun x : ℝ => (radialRadius n : ℂ) * Complex.exp (x * Complex.I)) := by
      fun_prop
    have hcomp := ((hF _ (im_diskToUpperHalfPlane_pos hw).le).comp
      (analyticAt_diskToUpperHalfPlane' (ne_one_of_norm_lt_one hw))).continuousAt
    exact hcomp.comp (f := fun x : ℝ => (radialRadius n : ℂ) * Complex.exp (x * Complex.I))
      hc.continuousAt
  · filter_upwards with n
    filter_upwards with φ
    intro _hφ
    exact hM _ (im_diskToUpperHalfPlane_pos (norm_radial_circle_lt_one' n φ)).le
  · exact intervalIntegrable_const
  · filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (2 * Real.pi)] with φ hφ0 hφ2 hφmem
    have hpi : 0 < 2 * Real.pi := by positivity
    have hIoc : φ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      simpa [Set.uIoc_of_le hpi.le] using hφmem
    have hφ : φ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
      ⟨hIoc.1, lt_of_le_of_ne hIoc.2 hφ2⟩
    have hhalf : 0 < φ / 2 := div_pos hφ.1 (by norm_num)
    have hhalfpi : φ / 2 < Real.pi := by nlinarith [hφ.2]
    have hsinpos := Real.sin_pos_of_pos_of_lt_pi hhalf hhalfpi
    have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
      conv_lhs => rw [show φ = 2 * (φ / 2) by ring]
      exact Real.cos_two_mul (φ / 2)
    have hone : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
      rw [hc]
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
    have hexp : Complex.exp (φ * Complex.I) ≠ 1 := by
      intro he
      rw [Complex.exp_ofReal_mul_I] at he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, Complex.one_re] at hre
      nlinarith [hone, sq_pos_of_pos hsinpos]
    have hcircle : Tendsto
        (fun n : ℕ => (radialRadius n : ℂ) * Complex.exp (φ * Complex.I))
        atTop (𝓝 (Complex.exp (φ * Complex.I))) := by
      simpa using (Complex.ofRealCLM.continuous.tendsto 1).comp
        tendsto_radialRadius' |>.mul_const (Complex.exp (φ * Complex.I))
    have hcayley : Tendsto
        (fun n : ℕ => diskToUpperHalfPlane
          ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))
        atTop
        (𝓝 (diskToUpperHalfPlane (Complex.exp (φ * Complex.I)))) :=
      (analyticAt_diskToUpperHalfPlane' hexp).continuousAt.tendsto.comp hcircle
    have hb : 0 ≤ (diskToUpperHalfPlane (Complex.exp (φ * Complex.I))).im := by
      rw [im_diskToUpperHalfPlane _ hexp, ← Complex.sq_norm]
      simp
    have ht := (hF _ hb).continuousAt.tendsto.comp hcayley
    rw [diskToUpperHalfPlane_exp_mul_I hφ] at ht
    exact ht

/-- **Bounded Cauchy–Poisson formula** (the analytic step of the dilation variance lemma).
Law: the standard real Cauchy density `standardCauchyWeight t = 1/(π(1+t²))` (Lebesgue
integral). Domain: `F : ℂ → E`, `E` a complex Banach space, analytic at every `w` with
`0 ≤ Im w` (the closed upper half-plane; analyticity at real points is the hypothesis
used for boundary continuity) and bounded there by `M`. Conclusion: the Cauchy
average of the boundary values equals the value at `i`. -/
theorem integral_standardCauchyWeight_smul_eq_of_analyticAt
    (F : ℂ → E) (hF : ∀ w : ℂ, 0 ≤ w.im → AnalyticAt ℂ F w)
    (M : ℝ) (hM : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ M) :
    (∫ t : ℝ, standardCauchyWeight t • F (t : ℂ)) = F Complex.I := by
  let J : ℕ → E := fun n =>
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      F (diskToUpperHalfPlane ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))
  let L : E := ∫ φ in (0 : ℝ)..(2 * Real.pi), F (Real.tan (φ / 2 - Real.pi / 2) : ℂ)
  have hJ : Tendsto J atTop (𝓝 L) :=
    tendsto_radial_integral_comp_diskToUpperHalfPlane F hF M hM
  have hmean : ∀ n : ℕ, (2 * Real.pi)⁻¹ • J n = F Complex.I := by
    intro n
    have h := circleAverage_comp_diskToUpperHalfPlane F hF (radialRadius_nonneg' n)
      (radialRadius_lt_one' n)
    rw [Real.circleAverage_def] at h
    simpa [J, circleMap_zero] using h
  have hnorm : Tendsto (fun n => (2 * Real.pi)⁻¹ • J n) atTop
      (𝓝 ((2 * Real.pi)⁻¹ • L)) := hJ.const_smul _
  have hangular : (2 * Real.pi)⁻¹ • L = F Complex.I :=
    tendsto_nhds_unique hnorm
      (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hmean n).symm))
  rw [integral_standardCauchyWeight_smul_eq_circleParam (fun t : ℝ => F (t : ℂ))]
  exact hangular

end Poisson

section CauchyLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard Cauchy law `ProbabilityTheory.cauchyMeasure 0 1` has density
`standardCauchyWeight t = 1/(π(1+t²))` with respect to Lebesgue measure (totalized
integrals; no integrability hypothesis). -/
theorem integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul (f : ℝ → E) :
    (∫ t, f t ∂ProbabilityTheory.cauchyMeasure 0 1) =
      ∫ t : ℝ, standardCauchyWeight t • f t := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_cauchyPDF 0 1)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  congr 1
  rw [ProbabilityTheory.cauchyPDF, ENNReal.toReal_ofReal
      (ProbabilityTheory.cauchyPDF_pos 0 one_ne_zero t).le,
    ProbabilityTheory.cauchyPDFReal]
  unfold standardCauchyWeight
  simp only [NNReal.coe_one, mul_one, sub_zero, one_pow]
  field_simp
  ring

/-- Symmetry of the standard Cauchy law under `t ↦ -t`. -/
theorem integral_cauchyMeasure_comp_neg (f : ℝ → E) :
    (∫ t, f (-t) ∂ProbabilityTheory.cauchyMeasure 0 1) =
      ∫ t, f t ∂ProbabilityTheory.cauchyMeasure 0 1 := by
  rw [integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul,
    integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul]
  rw [← integral_neg_eq_self (fun t => standardCauchyWeight t • f t)]
  congr 1
  funext t
  unfold standardCauchyWeight
  simp

end CauchyLaw

end BlockBand.Critical.Collar
