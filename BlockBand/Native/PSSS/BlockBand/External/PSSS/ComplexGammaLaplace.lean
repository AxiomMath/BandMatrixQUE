module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioProductFubini
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected

/-!
# The Gamma integral with the APSSS complex Laplace rate

This file proves the complex-rate Laplace/Gamma identity on the open right half-plane.
The branch is Mathlib's principal `Complex.cpow`: the right half-plane lies in the
slit plane, so analytic continuation from positive real rates fixes the branch
uniquely.  The proof also supplies the absolute-integrability and holomorphy facts
needed to pass from the iterated Fourier integral to the explicit APSSS transform.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory Set
open scoped Topology

/-- Pointwise absolute value of the complex-rate Gamma kernel on the positive ray. -/
theorem norm_complexGammaKernel {a w : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w)‖ =
      Real.exp (-w.re * y) * y ^ (a.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re,
    Complex.one_re, Complex.norm_exp]
  have hre : (-(y : ℂ) * w).re = -w.re * y := by
    simp [Complex.mul_re, mul_comm]
  rw [hre]
  ring

/-- Integrability of the positive-real-rate Gamma kernel, made explicit because it
is the majorant for the complex-rate kernel. -/
theorem integrableOn_complexGammaKernel_ofReal {a : ℂ} {r : ℝ}
    (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ =>
      (y : ℂ) ^ (a - 1) * Complex.exp (-(r * y))) (Ioi 0) := by
  have hval := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := a) (r := r) ha hr
  by_contra h
  have hz : (∫ y : ℝ in Ioi 0,
      (y : ℂ) ^ (a - 1) * Complex.exp (-(r * y))) = 0 := integral_undef h
  have hne : (1 / r : ℂ) ^ a * Complex.Gamma a ≠ 0 := by
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos ha)
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (one_div_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')))
  exact hne (hval ▸ hz)

/-- Continuity of the Gamma kernel on the open positive ray. -/
theorem continuousOn_complexGammaKernel (a w : ℂ) :
    ContinuousOn (fun y : ℝ =>
      (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w)) (Ioi 0) := by
  intro y hy
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact (continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 hy)).comp Complex.continuous_ofReal.continuousAt
  · exact Complex.continuous_exp.continuousAt.comp
      (((continuous_neg.comp Complex.continuous_ofReal).mul continuous_const).continuousAt)

/-- Absolute integrability of the Gamma kernel for every rate in the open right
half-plane. -/
theorem integrableOn_complexGammaKernel {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ =>
      (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w)) (Ioi 0) := by
  have hreal := integrableOn_complexGammaKernel_ofReal
    (a := a) (r := w.re) ha hw
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w))
      (volume.restrict (Ioi 0)) :=
    (continuousOn_complexGammaKernel a w).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (μ := volume.restrict (Ioi 0)) hreal.norm hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hrealnorm :
      ‖(y : ℂ) ^ (a - 1) * Complex.exp (-(w.re * y))‖ =
        Real.exp (-w.re * y) * y ^ (a.re - 1) := by
    simpa [mul_comm (y : ℂ)] using
      (norm_complexGammaKernel (a := a) (w := (w.re : ℂ)) hy)
  rw [norm_complexGammaKernel hy, hrealnorm]

/-- Differentiation under the integral sign for the complex decay rate. -/
theorem hasDerivAt_complexGammaIntegral {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    HasDerivAt
      (fun w' => ∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w'))
      (∫ y : ℝ in Ioi 0,
        -((y : ℂ) * ((y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w)))) w := by
  let r : ℝ := w.re / 2
  let s : Set ℂ := {w' | r < w'.re}
  have hδ : 0 < r := half_pos hw
  have hs : s ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hw)
  let F : ℂ → ℝ → ℂ := fun w' y =>
    (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w')
  let F' : ℂ → ℝ → ℂ := fun w' y =>
    -((y : ℂ) * ((y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w')))
  let bound : ℝ → ℝ := fun y =>
    ‖(y : ℂ) ^ (((a.re : ℂ) + 1) - 1) * Complex.exp (-(r * y))‖
  have hF_meas : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w')
      (volume.restrict (Ioi 0)) := by
    filter_upwards [(Complex.isOpen_re_gt 0).eventually_mem hw] with w' hw'
    exact (integrableOn_complexGammaKernel ha hw').1
  have hinter := integrableOn_complexGammaKernel_ofReal
    (a := (a.re : ℂ) + 1) (r := r) (add_pos ha zero_lt_one) hδ
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := hinter.norm
  have hF'_meas : AEStronglyMeasurable (F' w)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    refine ContinuousAt.continuousWithinAt (ContinuousAt.neg (ContinuousAt.mul ?_ ?_))
    · exact Complex.continuous_ofReal.continuousAt
    · exact (continuousOn_complexGammaKernel a w y hy).continuousAt
        (isOpen_Ioi.mem_nhds hy)
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ∀ w' ∈ s,
      ‖F' w' y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have hle : r ≤ w'.re := le_of_lt hw'
    have hy1 : y * y ^ (a.re - 1) = y ^ a.re := by
      simpa [Real.rpow_one] using (Real.rpow_add hy 1 (a.re - 1)).symm
    have hre : (((a.re : ℂ) + 1) - 1).re = a.re := by simp
    have hLHS : ‖F' w' y‖ = Real.exp (-w'.re * y) * y ^ a.re := by
      unfold F'
      rw [norm_neg, norm_mul, norm_complexGammaKernel (a := a) (w := w') hy]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.le]
      calc
        y * (Real.exp (-w'.re * y) * y ^ (a.re - 1)) =
            Real.exp (-w'.re * y) * (y * y ^ (a.re - 1)) := by ring
        _ = Real.exp (-w'.re * y) * y ^ a.re := by rw [hy1]
    have hRHS : bound y = Real.exp (-r * y) * y ^ a.re := by
      simp only [bound, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, hre, Complex.norm_exp]
      simp [mul_comm]
    rw [hLHS, hRHS]
    gcongr
    · exact Real.rpow_nonneg hy.le _
    · exact hy.le
  have hdiff : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ∀ w' ∈ s,
      HasDerivAt (F · y) (F' w' y) w' := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have harg : HasDerivAt (fun w'' : ℂ => -(y : ℂ) * w'') (-(y : ℂ)) w' :=
      hasDerivAt_const_mul (-(y : ℂ))
    have hexp : HasDerivAt (fun w'' : ℂ => Complex.exp (-(y : ℂ) * w''))
        (Complex.exp (-(y : ℂ) * w') * (-(y : ℂ))) w' :=
      (Complex.hasDerivAt_exp _).comp w' harg
    refine (hexp.const_mul ((y : ℂ) ^ (a - 1))).congr_deriv ?_
    simp [F', mul_comm, mul_assoc, mul_neg, neg_mul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    hs hF_meas (integrableOn_complexGammaKernel ha hw) hF'_meas hbound
      hbound_int hdiff).2

/-- The complex-rate Gamma integral is analytic on the open right half-plane. -/
theorem analyticOnNhd_complexGammaIntegral {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ
      (fun w : ℂ => ∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w)) {w | 0 < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt 0)
  intro w hw
  exact (hasDerivAt_complexGammaIntegral ha hw).differentiableAt.differentiableWithinAt

/-- Complex-rate Laplace/Gamma identity with the principal `Complex.cpow` branch.
Both the exponent and the rate may be complex; only their real parts are required
positive. -/
theorem complexGammaIntegral_eq {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w) =
      w ^ (-a) * Complex.Gamma a := by
  let Ω : Set ℂ := {w | 0 < w.re}
  have hΩpre : IsPreconnected Ω := (convex_halfSpace_re_gt 0).isPreconnected
  let F : ℂ → ℂ := fun w' => ∫ y : ℝ in Ioi 0,
    (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * w')
  let G : ℂ → ℂ := fun w' => w' ^ (-a) * Complex.Gamma a
  have hF : AnalyticOnNhd ℂ F Ω := analyticOnNhd_complexGammaIntegral ha
  have hG : AnalyticOnNhd ℂ G Ω := by
    intro w' hw'
    have hwslit : w' ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hw')
    exact (AnalyticAt.cpow analyticAt_id analyticAt_const hwslit).mul analyticAt_const
  have hpos : (1 : ℂ) ∈ Ω := by simp [Ω]
  refine hF.eqOn_of_preconnected_of_frequently_eq hG hΩpre hpos ?_ hw
  have hseq : Tendsto (fun n : ℕ => ((1 + (n + 1 : ℝ)⁻¹ : ℝ) : ℂ))
      atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hr : Tendsto (fun n : ℕ => (1 + (n + 1 : ℝ)⁻¹ : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    · filter_upwards with n hn
      have heq : (1 + (n + 1 : ℝ)⁻¹ : ℝ) = 1 := Complex.ofReal_injective hn
      have hpos' : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
      linarith
  refine hseq.frequently (Frequently.of_forall fun n => ?_)
  let r : ℝ := 1 + (n + 1 : ℝ)⁻¹
  have hr : 0 < r := by positivity
  have hreal := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := a) (r := r) ha hr
  have hcongr :
      (∫ y : ℝ in Ioi 0,
          (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * (r : ℂ))) =
        ∫ y : ℝ in Ioi 0,
          (y : ℂ) ^ (a - 1) * Complex.exp (-(r * y)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have he : -(y : ℂ) * (r : ℂ) = -(r * y : ℂ) := by
      simp [mul_comm]
    simp [he]
  have hpow : (1 / r : ℂ) ^ a = (r : ℂ) ^ (-a) := by
    rw [one_div, Complex.inv_cpow_ofReal_nonneg hr.le a, ← Complex.cpow_neg]
  calc
    F (r : ℂ) = ∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (a - 1) * Complex.exp (-(y : ℂ) * (r : ℂ)) := rfl
    _ = ∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (a - 1) * Complex.exp (-(r * y)) := hcongr
    _ = (1 / r : ℂ) ^ a * Complex.Gamma a := hreal
    _ = (r : ℂ) ^ (-a) * Complex.Gamma a := by rw [hpow]
    _ = G (r : ℂ) := rfl

end PSSSNative.BlockBand.PSSS
