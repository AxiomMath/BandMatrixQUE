module

public import Mathlib.Analysis.Complex.Poisson

/-!
# Kolmogorov conjugate bound: the Herglotz transform of `|Im f|`

For `f` with `DiffContOnCl ℂ f (ball 0 ρ)`, `0 < ρ`, `herglotzAbsIm f ρ` is the Herglotz–Riesz
integral of `|Im f|` on the circle of radius `ρ` (Mathlib `herglotzRieszKernel`). It is holomorphic
on `ball 0 ρ`, equals the circle average of `|Im f|` at `0`, and (Poisson formula for `f`, Mathlib
`DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`, positivity of the Poisson kernel)
its real part dominates `|Im f|` on `ball 0 ρ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Kolmogorov

open Complex Real Metric Set

/-- The Herglotz–Riesz integral of `|Im f|` on the circle of radius `ρ`. -/
def herglotzAbsIm (f : ℂ → ℂ) (ρ : ℝ) (w : ℂ) : ℂ :=
  circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • ((|(f ζ).im| : ℝ) : ℂ)) 0 ρ
/-- The Poisson kernel is nonnegative on the circle. -/
theorem re_herglotzRieszKernel_nonneg {ρ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) ρ)
    (hz : z ∈ sphere (0 : ℂ) ρ) : 0 ≤ (herglotzRieszKernel 0 w z).re := by
  have h := le_re_herglotzRieszKernel hz hw
  simp only [sub_zero] at h
  rw [herglotzRieszKernel_def]
  simp only [sub_zero]
  refine le_trans ?_ h
  have : ‖w‖ < ρ := by simpa using hw
  apply div_nonneg <;> linarith [norm_nonneg w]

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- `|Im f|` is circle integrable. -/
theorem circleIntegrable_absIm (hρ : 0 < ρ) (hf : DiffContOnCl ℂ f (ball 0 ρ)) :
    CircleIntegrable (fun ζ ↦ |(f ζ).im|) 0 ρ := by
  have hc : ContinuousOn f (sphere 0 ρ) :=
    hf.2.mono (sphere_subset_closedBall.trans_eq (closure_ball 0 hρ.ne').symm)
  exact ContinuousOn.circleIntegrable hρ.le (continuous_abs.comp_continuousOn
    (continuous_im.comp_continuousOn hc))

/-- `herglotzAbsIm f ρ` is holomorphic on `ball 0 ρ`. -/
theorem differentiableOn_herglotzAbsIm (hρ : 0 < ρ) (hf : DiffContOnCl ℂ f (ball 0 ρ)) :
    DifferentiableOn ℂ (herglotzAbsIm f ρ) (ball 0 ρ) := by
  have hi : CircleIntegrable (fun ζ ↦ ((|(f ζ).im| : ℝ) : ℂ)) 0 ρ := by
    have := circleIntegrable_absIm hρ hf
    simp only [CircleIntegrable, intervalIntegrable_iff] at this ⊢
    exact Complex.ofRealCLM.integrable_comp this
  refine (differentiableOn_circleAverage_herglotzRieszKernel_smul hi).mono ?_
  intro w hw hws
  rw [abs_of_pos hρ] at hws
  have h1 : ‖w‖ < ρ := by simpa using hw
  have h2 : ‖w‖ = ρ := by simpa using hws
  linarith

/-- At the centre, `herglotzAbsIm f ρ` is the circle average of `|Im f|`. -/
theorem herglotzAbsIm_zero (hρ : 0 < ρ) (hf : DiffContOnCl ℂ f (ball 0 ρ)) :
    herglotzAbsIm f ρ 0 = ((circleAverage (fun ζ ↦ |(f ζ).im|) 0 ρ : ℝ) : ℂ) := by
  unfold herglotzAbsIm
  rw [circleAverage_congr_sphere (f₂ := Complex.ofRealCLM ∘ (fun ζ ↦ |(f ζ).im|))]
  · exact Complex.ofRealCLM.circleAverage_comp_comm (circleIntegrable_absIm hρ hf)
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [abs_of_pos hρ] at hz
      simp at hz; linarith
    simp [herglotzRieszKernel_def, div_self hz0]

/-- Poisson domination: `|Im f w| ≤ re (herglotzAbsIm f ρ w)` on `ball 0 ρ`. -/
theorem abs_im_le_re_herglotzAbsIm (hρ : 0 < ρ) (hf : DiffContOnCl ℂ f (ball 0 ρ)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) ρ) : |(f w).im| ≤ (herglotzAbsIm f ρ w).re := by
  have hws : w ∉ sphere (0 : ℂ) |ρ| := by
    intro h
    rw [abs_of_pos hρ] at h
    have h1 : ‖w‖ < ρ := by simpa using hw
    have h2 : ‖w‖ = ρ := by simpa using h
    linarith
  have hc : ContinuousOn f (sphere 0 ρ) :=
    hf.2.mono (sphere_subset_closedBall.trans_eq (closure_ball 0 hρ.ne').symm)
  have hK : ContinuousOn (herglotzRieszKernel 0 w) (sphere 0 ρ) := by
    have := continuousOn_herglotzRieszKernel_sphere (c := 0) hws
    rwa [abs_of_pos hρ] at this
  have hP := hf.circleAverage_re_herglotzRieszKernel_smul hw
  have hint : CircleIntegrable ((re ∘ herglotzRieszKernel 0 w) • f) 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le
      ((continuous_re.comp_continuousOn hK).smul hc)
  have him : (f w).im = circleAverage
      (fun ζ ↦ (herglotzRieszKernel 0 w ζ).re * (f ζ).im) 0 ρ := by
    rw [← hP, ← Complex.imCLM_apply, ← imCLM.circleAverage_comp_comm hint]
    congr 1
    funext ζ
    simp
  have hre : (herglotzAbsIm f ρ w).re = circleAverage
      (fun ζ ↦ (herglotzRieszKernel 0 w ζ).re * |(f ζ).im|) 0 ρ := by
    unfold herglotzAbsIm
    rw [re_circleAverage_herglotzRieszKernel_smul (circleIntegrable_absIm hρ hf) hws]
    rfl
  rw [him, hre]
  refine abs_circleAverage_le_circleAverage_abs.trans (le_of_eq ?_)
  apply circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hρ] at hz
  simp only [Pi.abs_apply, abs_mul, abs_of_nonneg (re_herglotzRieszKernel_nonneg hw hz)]

end BlockBand.SourceProcess.Kolmogorov
