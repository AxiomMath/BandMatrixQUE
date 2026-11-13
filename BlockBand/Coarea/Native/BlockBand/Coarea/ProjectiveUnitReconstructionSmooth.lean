module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairAnalyticCarriers

/-!
# Smoothness of phase-fixed affine projective reconstruction

The chart-origin derivative used by the local Jacobian is only one point of the
phase-fixed affine chart.  This module proves the complementary global analytic
fact: normalization of the affine representative is real differentiable at every
projective coordinate.  This is the global smoothness input needed before the
Householder completion can be treated entrywise on the coherent analytic carriers.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized affine representative is real differentiable at every point of
its phase-fixed projective chart. -/
theorem differentiableAt_projectiveUnitReconstruction
    (k : ι) (z : ProjectiveChartCoordinate k → ℂ) :
    DifferentiableAt ℝ (projectiveUnitReconstruction k) z := by
  have hr :=
    (hasFDerivAt_projectiveEigenvectorReconstruction k z).differentiableAt
  have hn : DifferentiableAt ℝ
      (fun w : ProjectiveChartCoordinate k → ℂ =>
        ‖projectiveEigenvectorReconstruction k w‖) z :=
    hr.norm ℂ (projectiveEigenvectorReconstruction_ne_zero k z)
  have hi : DifferentiableAt ℝ
      (fun w : ProjectiveChartCoordinate k → ℂ =>
        ‖projectiveEigenvectorReconstruction k w‖⁻¹) z :=
    hn.inv (norm_ne_zero_iff.mpr
      (projectiveEigenvectorReconstruction_ne_zero k z))
  change DifferentiableAt ℝ
    (fun w : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k w‖⁻¹ •
        projectiveEigenvectorReconstruction k w) z
  exact hi.smul hr

/-- The normalized affine reconstruction is differentiable on the whole chart. -/
theorem differentiable_projectiveUnitReconstruction (k : ι) :
    Differentiable ℝ (projectiveUnitReconstruction k) :=
  fun z => differentiableAt_projectiveUnitReconstruction k z

/-- Coherent transport removes the competing `PiLp` instance paths and retains
global differentiability of projective normalization. -/
theorem differentiableAt_coherentProjectiveUnitReconstruction
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    DifferentiableAt ℝ (coherentProjectiveUnitReconstruction k) z := by
  exact (hasFDerivAt_coherentLift
    (differentiableAt_projectiveUnitReconstruction k z.value).hasFDerivAt).differentiableAt

/-- On the coherent carriers, the phase-fixed Householder completion is
differentiable entrywise, hence as a finite matrix, throughout the affine chart. -/
theorem differentiableAt_coherentProjectiveHouseholderFrame
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    DifferentiableAt ℝ (coherentProjectiveHouseholderFrame k) z := by
  have hu :=
    (differentiableAt_coherentProjectiveUnitReconstruction k z).hasFDerivAt
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  have hden :
      1 + ((coherentProjectiveUnitReconstruction k z).value k).re ≠ 0 := by
    change 1 + (projectiveUnitReconstruction k z.value k).re ≠ 0
    have hpos := projectiveUnitReconstruction_self_re_pos k z.value
    linarith
  exact ((hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry
    k a b (coherentProjectiveUnitReconstruction k z) hden).comp z hu).differentiableAt

/-- The coherent projective Householder frame is differentiable on its whole
affine chart. -/
theorem differentiable_coherentProjectiveHouseholderFrame (k : ι) :
    Differentiable ℝ (coherentProjectiveHouseholderFrame k) :=
  fun z => differentiableAt_coherentProjectiveHouseholderFrame k z

end CoareaNative.BlockBand
