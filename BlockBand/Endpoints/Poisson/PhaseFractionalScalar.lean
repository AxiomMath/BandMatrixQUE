module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Scalar subharmonic majorant for the projected fractional inverse

For `ζ` in the open unit disk and `0 < p < 1`,
`|1 - ζ|^{-p} ≤ K_p ∫_{(0,2π)} P_ζ(e^{iθ}) |1 - e^{iθ}|^{-p} dθ`, with
`P_ζ(z) = (|z|² - |ζ|²)/|z - ζ|²` Mathlib's Poisson kernel (`_root_.poissonKernel 0 ζ`) and
`K_p = 2^p / (2π cos(pπ/2))`; and the boundary weight is integrable:
`∫_{(0,2π)} |1 - e^{iθ}|^{-p} dθ < ∞`.

The paper invokes subharmonicity of `|1 - z|^{-p}`. We use instead the Poisson integral formula
(Mathlib `DiffContOnCl.circleAverage_poissonKernel_smul`) for the holomorphic functions
`(1 - r z)^{-p}`, `0 < r < 1`, the bound `cos(pπ/2)|u|^{-p} ≤ Re u^{-p} ≤ |u|^{-p}` for
`Re u > 0`, and `r ↑ 1`; this changes only the constant (by `1/cos(pπ/2)`), which is absorbed
in `C_p`.

Integrals over the circle are lower Lebesgue integrals over `θ ∈ (0, 2π)`, in `ℝ≥0∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open MeasureTheory Complex Metric Set Filter Topology
open scoped Real ENNReal

/-- `Re u^{-p} = |u|^{-p} cos(p arg u)` for `u ≠ 0` (principal branch). -/
theorem re_cpow_neg_ofReal {u : ℂ} (hu : u ≠ 0) (p : ℝ) :
    (u ^ (-(p : ℂ))).re = ‖u‖ ^ (-p) * Real.cos (p * arg u) := by
  rw [cpow_def_of_ne_zero hu, exp_re]
  have h1 : (log u * -(p : ℂ)).re = Real.log ‖u‖ * -p := by
    simp [log_re]
  have h2 : (log u * -(p : ℂ)).im = -(p * arg u) := by
    simp [log_im]; ring
  rw [h1, h2, Real.cos_neg, Real.rpow_def_of_pos (norm_pos_iff.mpr hu)]

/-- For `Re u > 0` and `0 ≤ p ≤ 1`: `cos(pπ/2)|u|^{-p} ≤ Re u^{-p} ≤ |u|^{-p}`. -/
theorem re_cpow_neg_bounds {u : ℂ} (hu : 0 < u.re) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.cos (p * π / 2) * ‖u‖ ^ (-p) ≤ (u ^ (-(p : ℂ))).re ∧
      (u ^ (-(p : ℂ))).re ≤ ‖u‖ ^ (-p) := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  rw [re_cpow_neg_ofReal hu0]
  have hpos : 0 ≤ ‖u‖ ^ (-p) := Real.rpow_nonneg (norm_nonneg _) _
  have harg : |arg u| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  refine ⟨?_, ?_⟩
  · rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hpos
    rw [← Real.cos_abs (p * arg u), abs_mul, abs_of_nonneg hp0]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · nlinarith [Real.pi_pos]
    · have : p * |arg u| ≤ p * (π / 2) := mul_le_mul_of_nonneg_left harg.le hp0
      linarith
  · calc ‖u‖ ^ (-p) * Real.cos (p * arg u) ≤ ‖u‖ ^ (-p) * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one _) hpos
      _ = ‖u‖ ^ (-p) := mul_one _

/-- On the unit circle, `|1 - z| ≤ 2 |1 - r z|` for `0 ≤ r ≤ 1`. -/
theorem norm_one_sub_le_two_mul {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖1 - z‖ ≤ 2 * ‖1 - (r : ℂ) * z‖ := by
  have h1 : ‖1 - z‖ ≤ ‖1 - (r : ℂ) * z‖ + ‖(r : ℂ) * z - z‖ := by
    have := norm_add_le (1 - (r : ℂ) * z) ((r : ℂ) * z - z)
    simpa using this
  have h2 : ‖(r : ℂ) * z - z‖ = 1 - r := by
    rw [show (r : ℂ) * z - z = ((r - 1 : ℝ) : ℂ) * z by push_cast; ring, norm_mul, hz,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have h3 : 1 - r ≤ ‖1 - (r : ℂ) * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
    rw [norm_mul, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
    simpa using this
  linarith

/-- The radially regulated test function `f_r(z) = (1 - r z)^{-p}`. -/
def radialPow (p r : ℝ) (z : ℂ) : ℂ := (1 - (r : ℂ) * z) ^ (-(p : ℂ))

theorem re_one_sub_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 < (1 - (r : ℂ) * z).re := by
  have h : |((r : ℂ) * z).re| ≤ ‖(r : ℂ) * z‖ := abs_re_le_norm _
  have h2 : ‖(r : ℂ) * z‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    nlinarith [norm_nonneg z]
  simp only [sub_re, one_re]
  have := (abs_le.mp h).2
  linarith

theorem radialPow_diffContOnCl {p r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    DiffContOnCl ℂ (radialPow p r) (ball (0 : ℂ) 1) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (0 : ℂ) one_ne_zero]
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  apply DifferentiableAt.differentiableWithinAt
  unfold radialPow
  apply DifferentiableAt.cpow_const
  · fun_prop
  · exact Or.inl (re_one_sub_pos hr0 hr1 hz')

theorem poissonKernel_nonneg_of_mem_sphere {ζ z : ℂ} (hζ : ‖ζ‖ < 1) (hz : ‖z‖ = 1) :
    0 ≤ _root_.poissonKernel 0 ζ z := by
  rw [poissonKernel_def]
  simp only [sub_zero, hz]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg ζ]

theorem continuousOn_poissonKernel_sphere {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ContinuousOn (_root_.poissonKernel 0 ζ) (sphere (0 : ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa using hz
  have hne : z - ζ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hz1
    linarith
  apply ContinuousAt.continuousWithinAt
  rw [show _root_.poissonKernel 0 ζ = fun z => (‖z - 0‖ ^ 2 - ‖ζ - 0‖ ^ 2) /
    ‖(z - 0) - (ζ - 0)‖ ^ 2 from funext fun z => poissonKernel_def 0 ζ z]
  simp only [sub_zero]
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa using hne

theorem norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simp [norm_circleMap_zero]

/-- The Poisson formula for `f_r`, real part: `Re f_r(ζ) = (2π)⁻¹ ∫_0^{2π} P_ζ Re f_r`. -/
theorem re_radialPow_eq_circleAverage {ζ : ℂ} (hζ : ‖ζ‖ < 1) (p : ℝ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    (radialPow p r ζ).re =
      Real.circleAverage (fun z => _root_.poissonKernel 0 ζ z * (radialPow p r z).re) 0 1 := by
  have hP := (radialPow_diffContOnCl (p := p) hr0 hr1).circleAverage_poissonKernel_smul
    (w := ζ) (by simpa using hζ)
  have hci : CircleIntegrable (_root_.poissonKernel 0 ζ • radialPow p r) 0 1 := by
    apply ContinuousOn.circleIntegrable zero_le_one
    apply ContinuousOn.smul (continuousOn_poissonKernel_sphere hζ)
    have := (radialPow_diffContOnCl (p := p) hr0 hr1).continuousOn
    rw [closure_ball (0 : ℂ) one_ne_zero] at this
    exact this.mono sphere_subset_closedBall
  have h := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hci
  rw [hP, Complex.reCLM_apply] at h
  rw [← h]
  congr 1
  ext z
  simp

theorem circleMap_zero_one_eq (θ : ℝ) : circleMap 0 1 θ = exp (I * θ) := by
  rw [circleMap_zero, Complex.ofReal_one, one_mul, mul_comm]

/-- `|1 - e^{iθ}| ≥ (2/π) min(θ, 2π - θ)` for `θ ∈ [0, 2π]`. -/
theorem norm_one_sub_circleMap_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * π) :
    2 / π * min θ (2 * π - θ) ≤ ‖1 - circleMap 0 1 θ‖ := by
  rw [circleMap_zero_one_eq, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs]
  have hπ := Real.pi_pos
  rcases le_total θ π with h | h
  · have hs := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
    have : min θ (2 * π - θ) ≤ θ := min_le_left _ _
    have h2 : 2 / π * min θ (2 * π - θ) ≤ 2 / π * θ :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : 2 / π * θ = 2 * (2 / π * (θ / 2)) := by ring
    have h4 : 0 ≤ 2 / π * (θ / 2) := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hs := Real.mul_le_sin (x := π - θ / 2) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at hs
    have : min θ (2 * π - θ) ≤ 2 * π - θ := min_le_right _ _
    have h2 : 2 / π * min θ (2 * π - θ) ≤ 2 / π * (2 * π - θ) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : 2 / π * (2 * π - θ) = 2 * (2 / π * (π - θ / 2)) := by ring
    have h4 : 0 ≤ 2 / π * (π - θ / 2) := by
      apply mul_nonneg (by positivity); linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem norm_one_sub_circleMap_pos {θ : ℝ} (h : θ ∈ Ioo 0 (2 * π)) :
    0 < ‖1 - circleMap 0 1 θ‖ := by
  have := norm_one_sub_circleMap_ge h.1.le h.2.le
  have hm : 0 < min θ (2 * π - θ) := lt_min h.1 (by linarith [h.2])
  have : 0 < 2 / π * min θ (2 * π - θ) := mul_pos (by positivity) hm
  linarith

/-- Pointwise majorant of the boundary weight on `(0, 2π)`. -/
theorem boundaryWeight_le {p : ℝ} (hp0 : 0 ≤ p) {θ : ℝ} (h : θ ∈ Ioo 0 (2 * π)) :
    ‖1 - circleMap 0 1 θ‖ ^ (-p) ≤ (π / 2) ^ p * (θ ^ (-p) + (2 * π - θ) ^ (-p)) := by
  have hm : 0 < min θ (2 * π - θ) := lt_min h.1 (by linarith [h.2])
  have hπ := Real.pi_pos
  have hge := norm_one_sub_circleMap_ge h.1.le h.2.le
  have h1 : ‖1 - circleMap 0 1 θ‖ ^ (-p) ≤ (2 / π * min θ (2 * π - θ)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
  have h2 : (2 / π * min θ (2 * π - θ)) ^ (-p) = (π / 2) ^ p * (min θ (2 * π - θ)) ^ (-p) := by
    rw [Real.mul_rpow (by positivity) hm.le, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), inv_div]
  have h3 : (min θ (2 * π - θ)) ^ (-p) ≤ θ ^ (-p) + (2 * π - θ) ^ (-p) := by
    have ha : 0 ≤ θ ^ (-p) := Real.rpow_nonneg h.1.le _
    have hb : 0 ≤ (2 * π - θ) ^ (-p) := Real.rpow_nonneg (by linarith [h.2]) _
    rcases min_choice θ (2 * π - θ) with hc | hc <;> rw [hc] <;> linarith
  rw [h2] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The boundary weight `|1 - e^{iθ}|^{-p}`, `0 ≤ p < 1`, is integrable on `(0, 2π)`. -/
theorem lintegral_boundaryWeight_lt_top {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p)) < ∞ := by
  have hπ := Real.pi_pos
  set g : ℝ → ℝ := fun θ => (π / 2) ^ p * (θ ^ (-p) + (2 * π - θ) ^ (-p)) with hg
  have hint : IntervalIntegrable g volume 0 (2 * π) := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-p)) volume 0 (2 * π) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => (2 * π - x) ^ (-p)) volume 0 (2 * π) := by
      have := h1.comp_sub_left (2 * π)
      simpa using this.symm
    exact (h1.add h2).const_mul _
  have hint' : IntegrableOn g (Ioo 0 (2 * π)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hint).mono_set
      Ioo_subset_Ioc_self
  calc _ ≤ ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (g θ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact ENNReal.ofReal_le_ofReal (boundaryWeight_le hp0 hθ)
    _ < ∞ := hint'.lintegral_lt_top

/-- **Scalar Poisson majorant** (Step 4 of the phase fractional-inverse lemma).
For `|ζ| < 1` and `0 < p < 1`:
`cos(pπ/2) |1 - ζ|^{-p} ≤ (2^p/2π) ∫_{(0,2π)} P_ζ(e^{iθ}) |1 - e^{iθ}|^{-p} dθ`. -/
theorem ofReal_cos_mul_rpow_le_lintegral {ζ : ℂ} (hζ : ‖ζ‖ < 1) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ENNReal.ofReal (Real.cos (p * π / 2) * ‖1 - ζ‖ ^ (-p)) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p) *
        ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (_root_.poissonKernel 0 ζ (circleMap 0 1 θ)) *
          ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p)) := by
  have hπ := Real.pi_pos
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h] at hζ
    simp at hζ
  -- the bound for each radius `r ∈ (0,1)`
  have key : ∀ r ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.cos (p * π / 2) * ‖1 - (r : ℂ) * ζ‖ ^ (-p)) ≤
        ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p) *
          ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (_root_.poissonKernel 0 ζ (circleMap 0 1 θ)) *
            ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p)) := by
    intro r hr
    have hr0 := hr.1.le
    have hr1 := hr.2
    have hb := re_cpow_neg_bounds (re_one_sub_pos hr0 hr1 hζ.le) hp0.le hp1.le
    have hP := re_radialPow_eq_circleAverage hζ p hr0 hr1
    set g : ℝ → ℝ := fun θ => _root_.poissonKernel 0 ζ (circleMap 0 1 θ) *
      (radialPow p r (circleMap 0 1 θ)).re with hg
    have hci : CircleIntegrable (fun z => _root_.poissonKernel 0 ζ z * (radialPow p r z).re)
        0 1 := by
      apply ContinuousOn.circleIntegrable zero_le_one
      apply ContinuousOn.mul (continuousOn_poissonKernel_sphere hζ)
      have := (radialPow_diffContOnCl (p := p) hr0 hr1).continuousOn
      rw [closure_ball (0 : ℂ) one_ne_zero] at this
      exact (Complex.continuous_re.comp_continuousOn (this.mono sphere_subset_closedBall))
    have hgint : IntegrableOn g (Ioc 0 (2 * π)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hci
    have hgnn : ∀ θ, 0 ≤ g θ := by
      intro θ
      apply mul_nonneg (poissonKernel_nonneg_of_mem_sphere hζ (norm_circleMap_zero_one θ))
      have := re_cpow_neg_bounds (re_one_sub_pos hr0 hr1 (norm_circleMap_zero_one θ).le)
        hp0.le hp1.le
      have hc : 0 ≤ Real.cos (p * π / 2) := Real.cos_nonneg_of_mem_Icc
        ⟨by nlinarith, by nlinarith⟩
      exact le_trans (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _)) this.1
    have hpt : ∀ θ ∈ Ioo 0 (2 * π), ENNReal.ofReal (g θ) ≤
        ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (_root_.poissonKernel 0 ζ (circleMap 0 1 θ)) *
          ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p))) := by
      intro θ hθ
      have hz := norm_circleMap_zero_one θ
      have hPn := poissonKernel_nonneg_of_mem_sphere hζ hz
      have hub := (re_cpow_neg_bounds (re_one_sub_pos hr0 hr1 hz.le) hp0.le hp1.le).2
      have hpos := norm_one_sub_circleMap_pos hθ
      have h2 := norm_one_sub_le_two_mul hz hr0 hr1.le
      have h3 : ‖1 - (r : ℂ) * circleMap 0 1 θ‖ ^ (-p) ≤
          2 ^ p * ‖1 - circleMap 0 1 θ‖ ^ (-p) := by
        calc _ ≤ (‖1 - circleMap 0 1 θ‖ / 2) ^ (-p) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          _ = 2 ^ p * ‖1 - circleMap 0 1 θ‖ ^ (-p) := by
              rw [Real.div_rpow hpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
              field_simp
      rw [← ENNReal.ofReal_mul hPn, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc g θ ≤ _root_.poissonKernel 0 ζ (circleMap 0 1 θ) *
            (2 ^ p * ‖1 - circleMap 0 1 θ‖ ^ (-p)) := by
            apply mul_le_mul_of_nonneg_left _ hPn
            exact le_trans hub h3
        _ = _ := by ring
    calc ENNReal.ofReal (Real.cos (p * π / 2) * ‖1 - (r : ℂ) * ζ‖ ^ (-p))
        ≤ ENNReal.ofReal ((radialPow p r ζ).re) := ENNReal.ofReal_le_ofReal hb.1
      _ = ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), g θ) := by
          rw [hP, Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity),
            smul_eq_mul, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (g θ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall hgnn),
            setLIntegral_congr Ioo_ae_eq_Ioc.symm]
      _ ≤ ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal (_root_.poissonKernel 0 ζ (circleMap 0 1 θ)) *
              ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p))) := by
          gcongr 1
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
          exact hpt θ hθ
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
  -- the limit `r ↑ 1`
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (Real.cos (p * π / 2) *
      ‖1 - (r : ℂ) * ζ‖ ^ (-p))) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (Real.cos (p * π / 2) * ‖1 - ζ‖ ^ (-p)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun r : ℝ => ENNReal.ofReal (Real.cos (p * π / 2) *
        ‖1 - (r : ℂ) * ζ‖ ^ (-p))) 1 := by
      apply ENNReal.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.rpow_const (by fun_prop)
      left
      simpa using hζ1
    simpa using hc.tendsto
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact key r hr

end BlockBand.Endpoints.PhaseFractional
