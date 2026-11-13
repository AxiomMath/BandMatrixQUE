module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# The root kernel on the unit circle

For `0 ≤ s < 1` the kernel `θ ↦ |e^{iθ} - z|^{-s}` is integrable on the circle, with an integral
bounded uniformly in the complex root `z` (`circleAverage_root_kernel_le`). The proof reduces to a
nonnegative real radius by rotation and splits into small radii, which stay away from the circle,
and radii `≥ 1/2`, where the distance dominates the angle.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory
open scoped Real ENNReal

/-- The distance from the point `e^{iθ}` of the unit circle to a real radius `r`. -/
def radialDistance (r θ : ℝ) : ℝ := ‖Complex.exp ((θ : ℂ) * Complex.I) - (r : ℂ)‖

/-- The norm-square identity for the radial distance. -/
theorem radialDistance_sq (r θ : ℝ) :
    radialDistance r θ ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
  unfold radialDistance
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Angular separation `|θ| ≤ π · radialDistance r θ` for every `r ≥ 1/2`, with no upper bound
on `r`. -/
theorem abs_angle_le_pi_mul_radialDistance (r θ : ℝ)
    (hr : 1 / 2 ≤ r) (hθ : |θ| ≤ Real.pi) :
    |θ| ≤ Real.pi * radialDistance r θ := by
  have hd : 0 ≤ radialDistance r θ := norm_nonneg _
  have hp : 0 < Real.pi := Real.pi_pos
  have hc := Real.cos_le_one_sub_mul_cos_sq hθ
  have hone : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hmult : 1 - Real.cos θ ≤ 2 * r * (1 - Real.cos θ) := by
    nlinarith
  have heq := radialDistance_sq r θ
  have hsq : (|θ| / Real.pi) ^ 2 ≤ radialDistance r θ ^ 2 := by
    have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hp
    have hcc : 2 * θ ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos θ) := by
      have hquot : 2 * θ ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos θ := by
        convert sub_le_sub_left hc 1 using 1; ring
      simpa only [mul_comm] using (div_le_iff₀ hp2).mp hquot
    have hbase : θ ^ 2 ≤ Real.pi ^ 2 * radialDistance r θ ^ 2 := by
      nlinarith [sq_nonneg (1 - r), sq_nonneg θ]
    rw [div_pow, sq_abs]
    exact (div_le_iff₀ hp2).2 (by simpa only [mul_comm] using hbase)
  have hlin : |θ| / Real.pi ≤ radialDistance r θ :=
    (sq_le_sq₀ (div_nonneg (abs_nonneg θ) hp.le) hd).mp hsq
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hlin

/-- The inverse power of the radial distance is dominated by the inverse power of the angle,
for `θ ≠ 0`. -/
theorem radial_kernel_le_power (r θ s : ℝ) (hr : 1 / 2 ≤ r)
    (hθ : |θ| ≤ Real.pi) (hθne : θ ≠ 0) (hs : 0 ≤ s) :
    radialDistance r θ ^ (-s) ≤ Real.pi ^ s * |θ| ^ (-s) := by
  have hθpos : 0 < |θ| := abs_pos.mpr hθne
  have hl : |θ| / Real.pi ≤ radialDistance r θ :=
    (div_le_iff₀ Real.pi_pos).2 (by simpa only [mul_comm] using abs_angle_le_pi_mul_radialDistance r θ hr hθ)
  have hb := Real.rpow_le_rpow_of_nonpos (div_pos hθpos Real.pi_pos) hl (neg_nonpos.mpr hs)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hθpos.le Real.pi_pos.le, Real.rpow_neg Real.pi_pos.le]
  simp [div_eq_mul_inv, mul_comm]

/-- The reference angle singularity `|θ|^{-s}` is integrable on the centered period for `s < 1`. -/
theorem integrable_abs_angle_kernel (s : ℝ) (hs : s < 1) :
    IntegrableOn (fun θ : ℝ => |θ| ^ (-s)) (Set.Icc (-Real.pi) Real.pi) := by
  have hm : AEStronglyMeasurable (fun θ : ℝ => |θ| ^ (-s)) (volume : Measure ℝ) :=
    (continuous_abs.measurable.pow_const (-s)).aestronglyMeasurable
  have hd : ∀ᵐ θ : ℝ ∂volume, ‖|θ| ^ (-s)‖ ≤ 1 * ‖θ‖ ^ (-s) := by
    filter_upwards with θ
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg θ) _)]
  have hloc := locallyIntegrable_of_norm_le_rpow (E := ℝ) (by simp)
    (by simpa using hs) hd hm
  exact hloc.integrableOn_isCompact isCompact_Icc

/-- Unit-circle distances to radii below 1/2 are uniformly separated from zero. -/
theorem half_le_radialDistance (r θ : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    1 / 2 ≤ radialDistance r θ := by
  have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
  have h := norm_sub_norm_le (Complex.exp ((θ : ℂ) * Complex.I)) (r : ℂ)
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
  unfold radialDistance
  linarith

/-- The radial root kernel for a small root has a uniform bound. -/
theorem radial_kernel_small_radius (r θ s : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hs : 0 ≤ s) : radialDistance r θ ^ (-s) ≤ (2 : ℝ) ^ s := by
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
    (half_le_radialDistance r θ hr hrhalf) (neg_nonpos.mpr hs)
  refine h.trans_eq ?_
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num)]
  simp

/-- Integrability of the radial root kernel; the only singular angle is a Lebesgue null
singleton. -/
theorem integrable_radial_kernel (r s : ℝ) (hr : 0 ≤ r) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IntegrableOn (fun θ : ℝ => radialDistance r θ ^ (-s)) (Set.Icc (-Real.pi) Real.pi) := by
  have hm : AEStronglyMeasurable (fun θ : ℝ => radialDistance r θ ^ (-s))
      (volume : Measure ℝ) := by
    have hc : Continuous (radialDistance r) := by unfold radialDistance; fun_prop
    exact (hc.measurable.pow_const (-s)).aestronglyMeasurable
  have hfin : volume (Set.Icc (-Real.pi) Real.pi) ≠ ∞ := by simp
  by_cases hrhalf : r ≤ 1 / 2
  · refine (integrableOn_const (C := (2 : ℝ) ^ s) (hs := hfin)).mono' hm.restrict ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ radialDistance r θ from norm_nonneg _) _)]
    exact radial_kernel_small_radius r θ s hr hrhalf hs0
  · refine ((integrable_abs_angle_kernel s hs1).const_mul (Real.pi ^ s)).mono' hm.restrict ?_
    have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ 0 := by
      rw [ae_iff]
      simp only [not_ne_iff]
      exact measure_singleton 0
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with θ hθ hθne
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ radialDistance r θ from norm_nonneg _) _)]
    exact radial_kernel_le_power r θ s (le_of_not_ge hrhalf)
      (abs_le.mpr hθ) hθne hs0

/-- An explicit radial integral majorant, depending only on `s`; its reference integral is finite
for `s < 1`. -/
def radialKernelMajorant (s : ℝ) : ℝ :=
  (2 : ℝ) ^ s * (2 * Real.pi) + Real.pi ^ s *
    ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, |θ| ^ (-s)

/-- The integral of the radial kernel is bounded uniformly in `r ≥ 0`. -/
theorem integral_radial_kernel_le (r s : ℝ) (hr : 0 ≤ r) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, radialDistance r θ ^ (-s)) ≤
      radialKernelMajorant s := by
  have hi := integrable_radial_kernel r s hr hs0 hs1
  have hpower := integrable_abs_angle_kernel s hs1
  have hfin : volume (Set.Icc (-Real.pi) Real.pi) ≠ ∞ := by simp
  have hnonneg : 0 ≤ ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, |θ| ^ (-s) :=
    integral_nonneg (fun θ => Real.rpow_nonneg (abs_nonneg θ) _)
  have hfirst : 0 ≤ (2 : ℝ) ^ s * (2 * Real.pi) := by positivity
  have hsecond : 0 ≤ Real.pi ^ s *
      ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, |θ| ^ (-s) := by positivity
  by_cases hrhalf : r ≤ 1 / 2
  · have hb : (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, radialDistance r θ ^ (-s)) ≤
        ∫ _θ : ℝ in Set.Icc (-Real.pi) Real.pi, (2 : ℝ) ^ s :=
      integral_mono hi (integrableOn_const (hs := hfin)) (fun θ => radial_kernel_small_radius r θ s hr hrhalf hs0)
    have hconst : (∫ _θ : ℝ in Set.Icc (-Real.pi) Real.pi, (2 : ℝ) ^ s) =
        (2 : ℝ) ^ s * (2 * Real.pi) := by
      simp [integral_const, Real.pi_pos.le, smul_eq_mul]
      ring
    rw [hconst] at hb
    unfold radialKernelMajorant
    linarith
  · have hne : ∀ᵐ θ : ℝ ∂volume, θ ≠ 0 := by
      rw [ae_iff]
      simp only [not_ne_iff]
      exact measure_singleton 0
    have hb : (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, radialDistance r θ ^ (-s)) ≤
        ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, Real.pi ^ s * |θ| ^ (-s) := by
      apply integral_mono_ae hi (hpower.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with θ hθ hθne
      exact radial_kernel_le_power r θ s (le_of_not_ge hrhalf) (abs_le.mpr hθ) hθne hs0
    rw [integral_const_mul] at hb
    unfold radialKernelMajorant
    linarith

/-- An angular shift of the circle removes the argument of every complex root, including the zero
root. -/
theorem norm_circle_sub_root_add_arg (z : ℂ) (θ : ℝ) :
    ‖circleMap 0 1 (θ + z.arg) - z‖ = radialDistance ‖z‖ θ := by
  have hz : z = (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have he : Complex.exp (((θ + z.arg : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((z.arg : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  simp only [circleMap, Complex.ofReal_one, zero_add, one_mul]
  calc
    ‖Complex.exp (((θ + z.arg : ℝ) : ℂ) * Complex.I) - z‖ =
        ‖(Complex.exp ((θ : ℂ) * Complex.I) - (‖z‖ : ℂ)) *
          Complex.exp ((z.arg : ℂ) * Complex.I)‖ := by
      congr 1
      rw [he]
      calc
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((z.arg : ℂ) * Complex.I) - z =
            Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((z.arg : ℂ) * Complex.I) -
              (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) :=
          congrArg (fun u => Complex.exp ((θ : ℂ) * Complex.I) *
            Complex.exp ((z.arg : ℂ) * Complex.I) - u) hz
        _ = _ := by ring
    _ = radialDistance ‖z‖ θ := by
      rw [norm_mul]
      simp [Complex.norm_exp, radialDistance]

/-- The radial root kernel is periodic with the period of the circle. -/
theorem radial_kernel_periodic (r s : ℝ) :
    Function.Periodic (fun θ : ℝ => radialDistance r θ ^ (-s)) (2 * Real.pi) := by
  have h := (periodic_circleMap 0 1).comp (fun z : ℂ => ‖z - (r : ℂ)‖ ^ (-s))
  simpa only [Function.comp_def, circleMap, Complex.ofReal_one, zero_add, one_mul, radialDistance] using h

/-- Integrability of the radial kernel on every finite interval, from its integrability on the
centered period and periodicity. -/
theorem intervalIntegrable_radial_kernel (r s : ℝ) (hr : 0 ≤ r)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => radialDistance r θ ^ (-s)) volume a b := by
  have hi : IntervalIntegrable (fun θ : ℝ => radialDistance r θ ^ (-s)) volume
      (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).2
      (integrable_radial_kernel r s hr hs0 hs1)
  have hfull : IntervalIntegrable (fun θ : ℝ => radialDistance r θ ^ (-s)) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact hi
  exact (radial_kernel_periodic r s).intervalIntegrable Real.two_pi_pos.ne' hfull a b

/-- The root kernel is integrable on the normalized circle for every complex root and every
`s ∈ [0,1)`. -/
theorem circleIntegrable_root_kernel (z : ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    CircleIntegrable (fun w : ℂ => ‖w - z‖ ^ (-s)) 0 1 := by
  have hshift : IntervalIntegrable (fun θ : ℝ => ‖circleMap 0 1 (θ + z.arg) - z‖ ^ (-s))
      volume 0 (2 * Real.pi) := by
    simp_rw [norm_circle_sub_root_add_arg]
    exact intervalIntegrable_radial_kernel ‖z‖ s (norm_nonneg _) hs0 hs1 _ _
  have hraw := (IntervalIntegrable.comp_add_right_iff
    (f := fun θ : ℝ => ‖circleMap 0 1 θ - z‖ ^ (-s))
    (a := 0) (b := 2 * Real.pi) (c := z.arg) (by finiteness)).mp hshift
  have hperiod := (periodic_circleMap 0 1).comp (fun w : ℂ => ‖w - z‖ ^ (-s))
  unfold CircleIntegrable
  apply hperiod.intervalIntegrable Real.two_pi_pos.ne' (t := z.arg)
  simpa only [Function.comp_def, zero_add, add_zero, add_comm] using hraw

/-- A root-independent constant bounding the normalized-circle kernel integral. -/
def circleKernelMajorant (s : ℝ) : ℝ := (2 * Real.pi)⁻¹ * radialKernelMajorant s

/-- The normalized-circle integral of the inverse distance power is bounded uniformly in the
complex root, for `s ∈ [0,1)`. -/
theorem circleAverage_root_kernel_le (z : ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Real.circleAverage (fun w : ℂ => ‖w - z‖ ^ (-s)) 0 1 ≤ circleKernelMajorant s := by
  rw [Real.circleAverage_eq_integral_add z.arg]
  simp_rw [norm_circle_sub_root_add_arg]
  have hp := (radial_kernel_periodic ‖z‖ s).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [zero_add] at hp
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hp
  rw [hp]
  have hcenter : (∫ θ in -Real.pi..Real.pi, radialDistance ‖z‖ θ ^ (-s)) =
      ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, radialDistance ‖z‖ θ ^ (-s) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact integral_Icc_eq_integral_Ioc.symm
  rw [hcenter, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_radial_kernel_le ‖z‖ s (norm_nonneg _) hs0 hs1)
    (inv_nonneg.mpr Real.two_pi_pos.le)

end BlockBand.DeterminantScore.GaussianGradient
