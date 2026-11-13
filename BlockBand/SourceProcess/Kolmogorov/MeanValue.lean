module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Kolmogorov conjugate bound: the positive-real-part power estimate

* `cos_mul_norm_rpow_le_re_cpow`: for `0 < re z`, `0 < p ≤ 1`:
  `cos (p π / 2) ‖z‖ ^ p ≤ re (z ^ p)` (principal power, `|arg z| < π / 2`).
* `cos_mul_circleAverage_le`: for `g` holomorphic on `ball 0 ρ` (`ρ > 1`) with `0 < re g` there,
  the mean value property of `g ^ p` gives
  `cos (p π / 2) · circleAverage ‖g‖ ^ p 0 1 ≤ ‖g 0‖ ^ p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Kolmogorov

open Complex Real Metric Set

/-- For `0 < re z` and `0 < p ≤ 1`: `cos (p π / 2) ‖z‖ ^ p ≤ re (z ^ p)`. -/
theorem cos_mul_norm_rpow_le_re_cpow {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {z : ℂ}
    (hz : 0 < z.re) :
    Real.cos (p * π / 2) * ‖z‖ ^ p ≤ (z ^ (p : ℂ)).re := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  rw [cpow_def_of_ne_zero hz0, exp_re]
  have h1 : (log z * (p : ℂ)).re = Real.log ‖z‖ * p := by
    simp [log_re]
  have h2 : (log z * (p : ℂ)).im = arg z * p := by
    simp [log_im]
  rw [h1, h2, ← Real.rpow_def_of_pos (norm_pos_iff.mpr hz0), mul_comm]
  gcongr
  have harg : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Real.cos_abs (arg z * p), abs_mul, abs_of_pos hp0]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · nlinarith [Real.pi_pos]
  · nlinarith [abs_nonneg (arg z)]

/-- Mean value bound for a holomorphic function with positive real part: if `g` is holomorphic on
`ball 0 ρ`, `1 < ρ`, and `0 < re g` there, then
`cos (p π / 2) · circleAverage ‖g‖ ^ p 0 1 ≤ ‖g 0‖ ^ p`. -/
theorem cos_mul_circleAverage_le {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {g : ℂ → ℂ} {ρ : ℝ}
    (hρ : 1 < ρ) (hg : DifferentiableOn ℂ g (ball 0 ρ))
    (hre : ∀ z ∈ ball (0 : ℂ) ρ, 0 < (g z).re) :
    Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖g z‖ ^ p) 0 1 ≤ ‖g 0‖ ^ p := by
  set h : ℂ → ℂ := fun z ↦ g z ^ (p : ℂ) with h_def
  have hh : DifferentiableOn ℂ h (ball 0 ρ) := fun z hz ↦
    DifferentiableWithinAt.cpow_const (hg z hz) (Or.inl (hre z hz))
  have hsub : sphere (0 : ℂ) |1| ⊆ ball 0 ρ := by
    intro z hz
    simp only [abs_one, mem_sphere_iff_norm, sub_zero] at hz
    simpa [hz] using hρ
  have hcl : DiffContOnCl ℂ h (ball 0 |1|) :=
    hh.diffContOnCl_ball (closedBall_subset_ball (by simpa using hρ))
  have hmv : circleAverage h 0 1 = h 0 := hcl.circleAverage
  have hhi : CircleIntegrable h 0 1 := (hh.continuousOn.mono hsub).circleIntegrable'
  have hgi : CircleIntegrable (fun z ↦ Real.cos (p * π / 2) * ‖g z‖ ^ p) 0 1 :=
    ContinuousOn.circleIntegrable' (by
      refine continuousOn_const.mul ?_
      exact ((hg.continuousOn.mono hsub).norm).rpow_const (fun _ _ ↦ Or.inr hp0.le))
  have hre_avg : circleAverage (Complex.reCLM ∘ h) 0 1 = (h 0).re := by
    rw [reCLM.circleAverage_comp_comm hhi, hmv]; rfl
  have hri : CircleIntegrable (Complex.reCLM ∘ h) 0 1 :=
    (reCLM.continuous.comp_continuousOn (hh.continuousOn.mono hsub)).circleIntegrable'
  calc Real.cos (p * π / 2) * circleAverage (fun z ↦ ‖g z‖ ^ p) 0 1
      = circleAverage (fun z ↦ Real.cos (p * π / 2) * ‖g z‖ ^ p) 0 1 := by
        rw [← smul_eq_mul, ← circleAverage_fun_smul]; rfl
    _ ≤ circleAverage (Complex.reCLM ∘ h) 0 1 := by
        apply circleAverage_mono hgi hri
        intro z hz
        exact cos_mul_norm_rpow_le_re_cpow hp0 hp1 (hre z (hsub hz))
    _ = (h 0).re := hre_avg
    _ ≤ ‖h 0‖ := Complex.re_le_norm _
    _ = ‖g 0‖ ^ p := Complex.norm_cpow_real _ _

end BlockBand.SourceProcess.Kolmogorov
