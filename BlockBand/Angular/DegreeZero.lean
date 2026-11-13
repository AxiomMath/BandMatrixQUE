module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Scale-invariant functions

A function `h` on a real normed space is scale-invariant when `h(rz) = h(z)` for every
`r > 0`. Then `Dh(rz) = r⁻¹ Dh(z)`, differentiability transfers along the scaling, and in
finite dimension a scale-invariant `h` that is `C¹` off the origin satisfies
`|h| ≤ M` and `‖Dh(z)‖ ‖z‖ ≤ M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.DegreeZero

open Set

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `h` is invariant under positive real scaling. -/
def IsScaleInvariant (h : E → ℝ) : Prop := ∀ (z : E) (r : ℝ), 0 < r → h (r • z) = h z

/-- Scaling of the derivative of a scale-invariant function: `Dh(r z) = r⁻¹ Dh(z)`. -/
theorem fderiv_smul_of_scaleInvariant {h : E → ℝ} (hinv : IsScaleInvariant h) {z : E}
    (hd : DifferentiableAt ℝ h z) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ h (r • z) = r⁻¹ • fderiv ℝ h z := by
  have hfun : h = fun x => h (r⁻¹ • x) := by
    funext x
    exact (hinv x r⁻¹ (inv_pos.2 hr)).symm
  have hlin : HasFDerivAt (fun x : E => r⁻¹ • x) (r⁻¹ • ContinuousLinearMap.id ℝ E) (r • z) :=
    ((ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul r⁻¹
  have hpt : r⁻¹ • (r • z) = z := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hD : HasFDerivAt h (fderiv ℝ h z) (r⁻¹ • (r • z)) := by rw [hpt]; exact hd.hasFDerivAt
  have hcomp : HasFDerivAt (fun x => h (r⁻¹ • x))
      ((fderiv ℝ h z).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)) (r • z) := hD.comp (r • z) hlin
  conv_lhs => rw [hfun]
  rw [hcomp.fderiv]
  ext w
  simp

/-- A scale-invariant function that is differentiable off the origin is differentiable at
every positive multiple of a point where it is differentiable. -/
theorem differentiableAt_smul_of_scaleInvariant {h : E → ℝ} (hinv : IsScaleInvariant h)
    {z : E} (hd : DifferentiableAt ℝ h z) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ h (r • z) := by
  have hfun : h = fun x => h (r⁻¹ • x) := by
    funext x
    exact (hinv x r⁻¹ (inv_pos.2 hr)).symm
  have hpt : r⁻¹ • (r • z) = z := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [hfun]
  exact (by rw [hpt]; exact hd : DifferentiableAt ℝ h (r⁻¹ • (r • z))).comp (r • z)
    ((differentiableAt_id).const_smul r⁻¹)

/-- **Bounds for scale-invariant `C¹` functions.** If `h` is scale invariant and `C¹` on
`E \ {0}` (finite-dimensional `E`), then `h` is bounded and `‖Dh(z)‖ ‖z‖` is bounded off the
origin. -/
theorem exists_bound_of_scaleInvariant [FiniteDimensional ℝ E] {h : E → ℝ}
    (hinv : IsScaleInvariant h) (hc : ContDiffOn ℝ 1 h {z | z ≠ 0}) :
    ∃ M : ℝ, (∀ z, |h z| ≤ M) ∧ ∀ z, z ≠ 0 → ‖fderiv ℝ h z‖ * ‖z‖ ≤ M := by
  have hopen : IsOpen {z : E | z ≠ 0} := isOpen_ne
  have hsub : Metric.sphere (0 : E) 1 ⊆ {z | z ≠ 0} := by
    intro z hz
    have : ‖z‖ = 1 := by simpa using hz
    intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hK : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn ((hc.continuousOn).mono hsub)
  have hcd : ContinuousOn (fderiv ℝ h) {z | z ≠ 0} :=
    hc.continuousOn_fderiv_of_isOpen hopen le_rfl
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn (hcd.mono hsub)
  refine ⟨max (max M₁ M₂) |h 0|, fun z => ?_, fun z hz => ?_⟩
  · by_cases hz : z = 0
    · rw [hz]; exact le_max_right _ _
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hn.ne']
    have := hM₁ _ hu
    rw [hinv z _ (inv_pos.2 hn), Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hn.ne']
    have hdz : DifferentiableAt ℝ h z :=
      (hc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
    have hs := fderiv_smul_of_scaleInvariant hinv hdz (inv_pos.2 hn)
    have := hM₂ _ hu
    rw [hs, norm_smul, Real.norm_eq_abs, abs_inv, abs_inv, abs_of_pos hn, inv_inv] at this
    have : ‖fderiv ℝ h z‖ * ‖z‖ ≤ M₂ := by linarith
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))

end BlockBand.Angular.DegreeZero
