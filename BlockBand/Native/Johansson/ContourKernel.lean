module

public import BlockBand.Native.Johansson.ContourKernelLine
public import BlockBand.Native.Johansson.ContourKernelCircle

/-!
# Johansson's formula (2.18): the contour form of the kernel

The double contour integral of the kernel integrand equals the correlation kernel.

* `verticalIntegrable_holds : VerticalIntegrableStatement`: for `‖z‖ = R` the line integrand
  `y ↦ i K(z, L + iy)` is Lebesgue integrable on `ℝ`;
* `circleIntegrable_holds : CircleIntegrableStatement`;
* `contourKernel_holds : ContourKernelStatement`: `kernel S d R L u v = sourceKernel S d u v`.

Proof. On `|z| = R`, `w = L + iy`: `|exp((w² - 2vw - z² + 2uz)/(2S))| ≤ C e^{-y²/(2S)}`,
`|w - z| ≥ L - R`, `|z - d_j| ≥ R - |d_j|`, and `∏_j |w - d_j|` is a polynomial in `|y|`
(`contour_norm_kernelIntegrand_le`), uniformly in `z`. This gives the line integrability, joint
integrability on `(0, 2π] × ℝ` (`contour_integrable_prod`), hence the circle integrability and the
Fubini swap. For fixed `y` the circle
integral is `circle_integral_kernelIntegrand`; the remaining line integrals are
`line_integral_heatInv`; the constants combine to `p_S(u - d_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory Polynomial Complex Metric
open BlockBand.External.Johansson
open scoped NNReal Real

theorem contour_norm_kernelIntegrand_le {N : ℕ} (S : ℝ≥0) (hS : 0 < S) {d : Fin N → ℝ} {R L : ℝ}
    (hC : AdmissibleContours d R L) (u v : ℝ) (z : ℂ) (hz : ‖z‖ = R) (y : ℝ) :
    ‖kernelIntegrand S d u v z ((L : ℂ) + y * I)‖ ≤
      (Real.exp ((L ^ 2 - 2 * v * L + R ^ 2 + 2 * |u| * R) / (2 * (S : ℝ))) / (L - R) *
        ∏ j, (R - |d j|)⁻¹) *
      ∑ k ∈ Finset.range (((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).natDegree + 1),
        ‖((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).coeff k‖ *
          (|y| ^ k * Real.exp (-(y ^ 2) / (2 * (S : ℝ)))) := by
  obtain ⟨hR, hdR, hRL⟩ := hC
  set w : ℂ := (L : ℂ) + y * I with hw
  have hSpos : (0 : ℝ) < S := hS
  -- the exponential
  have hE : ‖cexp ((w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z) / (2 * (S : ℂ)))‖ ≤
      Real.exp ((L ^ 2 - 2 * v * L + R ^ 2 + 2 * |u| * R) / (2 * (S : ℝ))) *
        Real.exp (-(y ^ 2) / (2 * (S : ℝ))) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h2S : (2 * (S : ℂ)) = ((2 * (S : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [h2S, Complex.div_ofReal_re]
    have hre : (w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z).re =
        L ^ 2 - y ^ 2 - 2 * v * L - (z.re ^ 2 - z.im ^ 2) + 2 * u * z.re := by
      simp [hw, sq, mul_re]
    rw [hre, ← add_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hn : z.re ^ 2 + z.im ^ 2 = R ^ 2 := by
      rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
    have hzr : |z.re| ≤ R := hz ▸ Complex.abs_re_le_norm z
    have : u * z.re ≤ |u| * R := by
      calc u * z.re ≤ |u * z.re| := le_abs_self _
        _ = |u| * |z.re| := abs_mul _ _
        _ ≤ |u| * R := by gcongr
    nlinarith [sq_nonneg z.im]
  -- the Cauchy denominator
  have hD : ‖w - z‖⁻¹ ≤ (L - R)⁻¹ := by
    have h1 : L - R ≤ ‖w - z‖ := by
      have := Complex.re_le_norm z
      have h2 := Complex.re_le_norm (w - z)
      simp only [hw, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im] at h2
      rw [hz] at this
      nlinarith
    exact inv_anti₀ (by linarith) h1
  -- the source product
  have hP : ‖∏ j, (w - d j) / (z - d j)‖ ≤
      (∏ j, (R - |d j|)⁻¹) *
      ∑ k ∈ Finset.range (((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).natDegree + 1),
        ‖((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).coeff k‖ * |y| ^ k := by
    rw [Finset.prod_div_distrib, norm_div, div_eq_mul_inv, mul_comm]
    have he : ∏ j, (w - d j) = (∏ j, (X - C (d j : ℂ))).eval w := by
      simp [eval_prod]
    rw [he]
    refine mul_le_mul ?_ (line_norm_eval_le _ L y) (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => (inv_pos.mpr (by linarith [hdR j])).le)
    rw [norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    refine inv_anti₀ (by linarith [hdR j]) ?_
    have := norm_sub_norm_le z (d j : ℂ)
    rw [hz, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  unfold kernelIntegrand
  rw [norm_mul, norm_div, div_eq_mul_inv]
  calc _ ≤ (Real.exp ((L ^ 2 - 2 * v * L + R ^ 2 + 2 * |u| * R) / (2 * (S : ℝ))) *
        Real.exp (-(y ^ 2) / (2 * (S : ℝ)))) * (L - R)⁻¹ * ((∏ j, (R - |d j|)⁻¹) *
      ∑ k ∈ Finset.range (((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).natDegree + 1),
        ‖((∏ j, (X - C (d j : ℂ))).comp (C (L : ℂ) + C I * X)).coeff k‖ * |y| ^ k) := by
        gcongr
    _ = _ := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_eq_mul_inv]
      ring

/-- The bound of `contour_norm_kernelIntegrand_le`, as an integrable majorant uniform in `z`. -/
theorem contour_kernelIntegrand_majorant {N : ℕ} (S : ℝ≥0) (hS : 0 < S) {d : Fin N → ℝ}
    {R L : ℝ} (hC : AdmissibleContours d R L) (u v : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∀ z : ℂ, ‖z‖ = R → ∀ y : ℝ,
      ‖kernelIntegrand S d u v z ((L : ℂ) + y * I)‖ ≤ g y :=
  ⟨_, (integrable_finsetSum _ fun k _ =>
      (line_integrable_abs_pow_mul_gauss hS k).const_mul _).const_mul _,
    fun z hz y => contour_norm_kernelIntegrand_le S hS hC u v z hz y⟩

theorem contour_line_ne_of_norm_le {R L : ℝ} (hRL : R < L) {z : ℂ} (hz : ‖z‖ ≤ R) (y : ℝ) :
    (L : ℂ) + y * I ≠ z := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im] at h1
  have := Complex.re_le_norm z
  linarith

theorem contour_ne_node_of_norm_eq {N : ℕ} {d : Fin N → ℝ} {R L : ℝ}
    (hC : AdmissibleContours d R L) {z : ℂ} (hz : ‖z‖ = R) (j : Fin N) : z ≠ d j := by
  intro h
  have := hC.2.1 j
  rw [h, Complex.norm_real, Real.norm_eq_abs] at hz
  linarith

theorem contour_continuous_kernelIntegrand {N : ℕ} {X : Type*} [TopologicalSpace X] (S : ℝ≥0)
    (d : Fin N → ℝ) (u v : ℝ) {z w : X → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hwz : ∀ x, w x ≠ z x) (hzd : ∀ x j, z x ≠ d j) :
    Continuous (fun x => kernelIntegrand S d u v (z x) (w x)) := by
  unfold kernelIntegrand
  refine (Continuous.div (by fun_prop) (hw.sub hz) fun x => sub_ne_zero.mpr (hwz x)).mul
    (continuous_finsetProd _ fun j _ => ?_)
  exact (hw.sub continuous_const).div (hz.sub continuous_const) fun x =>
    sub_ne_zero.mpr (hzd x j)

/-- **Line integrability**: the vertical line integrand is integrable, for every `z` on the circle. -/
theorem verticalIntegrable_holds : VerticalIntegrableStatement := by
  intro N _ S hS d _ R L hC u v z hz
  obtain ⟨g, hg, hb⟩ := contour_kernelIntegrand_majorant S hS hC u v
  refine hg.mono' ?_ (ae_of_all _ fun y => ?_)
  · refine (continuous_const.mul (contour_continuous_kernelIntegrand S d u v continuous_const
      (by fun_prop) (fun y => contour_line_ne_of_norm_le hC.2.2 hz.le y)
      fun _ j => contour_ne_node_of_norm_eq hC hz j)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_I, one_mul]
    exact hb z hz y

/-- Joint integrability on `(0, 2π] × ℝ` of the circle-line integrand, with a bounded continuous
factor `a(θ)` (used with `a = 1` and `a = deriv (circleMap 0 R)`). -/
theorem contour_integrable_prod {N : ℕ} (S : ℝ≥0) (hS : 0 < S) {d : Fin N → ℝ} {R L : ℝ}
    (hC : AdmissibleContours d R L) (u v : ℝ) {a : ℝ → ℂ} (ha : Continuous a) {A : ℝ}
    (hA : ∀ θ, ‖a θ‖ ≤ A) :
    Integrable (Function.uncurry fun θ y : ℝ =>
        a θ * (I * kernelIntegrand S d u v (circleMap 0 R θ) ((L : ℂ) + y * I)))
      ((volume.restrict (Set.uIoc 0 (2 * π))).prod volume) := by
  obtain ⟨g, hg, hb⟩ := contour_kernelIntegrand_majorant S hS hC u v
  have hcm : ∀ θ, ‖circleMap 0 R θ‖ = R := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hC.1]
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.mpr (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
  have hmaj : Integrable (fun p : ℝ × ℝ => A * g p.2)
      ((volume.restrict (Set.uIoc 0 (2 * π))).prod volume) :=
    (integrable_const A).mul_prod hg
  refine hmaj.mono' ?_ (ae_of_all _ fun p => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (ha.comp continuous_fst).mul (continuous_const.mul ?_)
    exact contour_continuous_kernelIntegrand S d u v ((continuous_circleMap 0 R).comp
      continuous_fst) (by fun_prop) (fun p => contour_line_ne_of_norm_le hC.2.2 (hcm p.1).le p.2)
      fun p j => contour_ne_node_of_norm_eq hC (hcm p.1) j
  · change ‖a p.1 * (I * kernelIntegrand S d u v (circleMap 0 R p.1) ((L : ℂ) + p.2 * I))‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul (hA p.1) (hb _ (hcm p.1) p.2) (norm_nonneg _)
      ((norm_nonneg _).trans (hA p.1))

/-- **Circle integrability**: `verticalIntegral` is integrable on the circle. -/
theorem circleIntegrable_holds : CircleIntegrableStatement := by
  intro N _ S hS d _ R L hC u v
  have h := (contour_integrable_prod S hS hC u v (a := fun _ => 1) continuous_const
    (A := 1) fun _ => by simp).integral_prod_left
  unfold CircleIntegrable
  rw [intervalIntegrable_iff]
  refine h.congr (ae_of_all _ fun θ => ?_)
  simp [verticalIntegral]

/-- Fubini: the circle integral of `verticalIntegral` is the line integral of circle integrals. -/
theorem contour_circleIntegral_verticalIntegral {N : ℕ} (S : ℝ≥0) (hS : 0 < S) {d : Fin N → ℝ}
    {R L : ℝ} (hC : AdmissibleContours d R L) (u v : ℝ) :
    circleIntegral (verticalIntegral S d u v L) 0 R =
      ∫ y : ℝ, ∮ z in C(0, R), I * kernelIntegrand S d u v z ((L : ℂ) + y * I) := by
  have h := contour_integrable_prod S hS hC u v (a := fun θ => circleMap 0 R θ * I)
    (by fun_prop) (A := R) fun θ => by
      rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hC.1]
  unfold circleIntegral
  simp_rw [deriv_circleMap, verticalIntegral, smul_eq_mul, ← integral_const_mul]
  exact intervalIntegral_integral_swap h

/-- The constants of `kernel`: `e^{(v²-u²)/2S} / ((2πi)² S) · i · 2πi · e^{(-a²+2ua)/2S}
· e^{-v²/2S} √(2πS) = p_S(u - a)`. -/
theorem contour_kernel_constant {S : ℝ≥0} (hS : 0 < S) (u v a : ℝ) (T : ℂ) :
    cexp (((v : ℂ) ^ 2 - (u : ℂ) ^ 2) / (2 * (S : ℂ))) /
        ((2 * (π : ℂ) * I) ^ 2 * (S : ℂ)) *
      (I * (2 * (π : ℂ) * I * (cexp ((-(a : ℂ) ^ 2 + 2 * (u : ℂ) * a) / (2 * (S : ℂ))) *
        (cexp (-(v : ℂ) ^ 2 / (2 * (S : ℂ))) * ((Real.sqrt (2 * π * S) : ℝ) : ℂ) * T)))) =
      (gaussKernel S a u : ℂ) * T := by
  have hS0 : (0 : ℝ) < S := hS
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hpos : (0 : ℝ) < 2 * π * S := by positivity
  set s : ℝ := Real.sqrt (2 * π * S) with hs_def
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hs2 : (s : ℂ) ^ 2 = 2 * π * S := by
    rw [← ofReal_pow, hs_def, Real.sq_sqrt hpos.le]; push_cast; ring
  have hexp : cexp (((v : ℂ) ^ 2 - (u : ℂ) ^ 2) / (2 * (S : ℂ))) *
      cexp ((-(a : ℂ) ^ 2 + 2 * (u : ℂ) * a) / (2 * (S : ℂ))) *
      cexp (-(v : ℂ) ^ 2 / (2 * (S : ℂ))) = cexp ((-(u - a) ^ 2 / (2 * S) : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [gaussKernel, ProbabilityTheory.gaussianPDFReal_def]
  simp only
  rw [← hs_def]
  calc _ = (cexp (((v : ℂ) ^ 2 - (u : ℂ) ^ 2) / (2 * (S : ℂ))) *
      cexp ((-(a : ℂ) ^ 2 + 2 * (u : ℂ) * a) / (2 * (S : ℂ))) *
      cexp (-(v : ℂ) ^ 2 / (2 * (S : ℂ)))) * (I * (2 * π * I) * s / ((2 * π * I) ^ 2 * S)) * T := by
        ring
    _ = _ := by
      rw [hexp]
      push_cast
      have : I * (2 * π * I) * (s : ℂ) / ((2 * π * I) ^ 2 * S) = (s : ℂ)⁻¹ := by
        field_simp
        linear_combination hs2
      rw [this]
      ring

/-- **The contour form** (2.18): `kernel S d R L u v = K(u, v)` on admissible contours. -/
theorem contourKernel_holds : ContourKernelStatement := by
  intro N hN S hS d hd R L hC u v
  have hcirc : ∀ y : ℝ, (∮ z in C(0, R), I * kernelIntegrand S d u v z ((L : ℂ) + y * I)) =
      I * (2 * π * I * ∑ j, cexp ((-(d j : ℂ) ^ 2 + 2 * (u : ℂ) * d j) / (2 * (S : ℂ))) *
        (cexp ((((L : ℂ) + y * I) ^ 2 - 2 * (v : ℂ) * ((L : ℂ) + y * I)) / (2 * (S : ℂ))) *
          ((lagrangeBasis d j).map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I))) := by
    intro y
    rw [circleIntegral.integral_const_mul,
      circle_integral_kernelIntegrand hN S hd hC u v _ (by simpa using hC.2.2)]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hint : ∀ j : Fin N, Integrable (fun y : ℝ =>
      cexp ((-(d j : ℂ) ^ 2 + 2 * (u : ℂ) * d j) / (2 * (S : ℂ))) *
        (cexp ((((L : ℂ) + y * I) ^ 2 - 2 * (v : ℂ) * ((L : ℂ) + y * I)) / (2 * (S : ℂ))) *
          ((lagrangeBasis d j).map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I))) :=
    fun j => (line_integrable_heat hS _ L v).const_mul _
  rw [kernel, contour_circleIntegral_verticalIntegral S hS hC u v]
  simp_rw [hcirc]
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ => hint j]
  simp_rw [integral_const_mul, line_integral_heatInv hS]
  rw [sourceKernel]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [biorthPoly]
  exact contour_kernel_constant hS u v (d j) _

end BlockBand.Native.Johansson
