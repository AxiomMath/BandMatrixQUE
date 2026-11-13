module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveUnitReconstructionDerivative
public import BlockBand.Coarea.Native.BlockBand.Coarea.HouseholderDerivativeIdentification

/-!
# Projective-coordinate derivative of the phase-fixed Householder frame

The phase-fixed unit representative is now differentiated through the explicit
Householder completion.  At the origin of an affine projective chart, its
matrix derivative has precisely the selected-row/selected-column form of an
infinitesimal eigenline rotation.  This is the nonlinear-to-linear tangent
bridge used in the local eigenpair Jacobian.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linearization of the phase-fixed Householder frame after
projective unit reconstruction, at the affine-chart origin. -/
def projectiveHouseholderFrameDifferential (k : ι) :
    (ProjectiveChartCoordinate k → ℂ) →ₗ[ℝ] Matrix ι ι ℂ :=
  (phaseFixedHouseholderAlgebraicDifferential k
      (projectiveSelectedVector k)).comp
    (projectiveChartTangentInsertion k)

/-- The nonlinear phase-fixed frame has the advertised projective-coordinate
Fréchet derivative at the chart origin. -/
theorem hasFDerivAt_phaseFixedHouseholderFrame_projective_zero (k : ι) :
    HasFDerivAt (fun z : ProjectiveChartCoordinate k → ℂ =>
      phaseFixedHouseholderFrame k (projectiveUnitReconstruction k z))
      (projectiveHouseholderFrameDifferential k).toContinuousLinearMap 0 := by
  have hunit := hasFDerivAt_projectiveUnitReconstruction_zero k
  have hden : 1 + (projectiveSelectedVector k k).re ≠ 0 := by
    change 1 + (projectiveEigenvectorReconstruction k 0 k).re ≠ 0
    simp
  have hframe := hasFDerivAt_phaseFixedHouseholderFrame_algebraic
    k (projectiveSelectedVector k) hden
  have hentry (a b : ι) : HasFDerivAt
      (fun z : ProjectiveChartCoordinate k → ℂ =>
        phaseFixedHouseholderFrame k (projectiveUnitReconstruction k z) a b)
      ((matrixEntryEvaluationCLM a b).comp
        (projectiveHouseholderFrameDifferential k).toContinuousLinearMap) 0 := by
    have ha := hasFDerivAt_pi'.mp hframe a
    have hab := hasFDerivAt_pi'.mp ha b
    have hab' : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => phaseFixedHouseholderFrame k w a b)
        ((ContinuousLinearMap.proj b).comp
          ((ContinuousLinearMap.proj a).comp
            (phaseFixedHouseholderAlgebraicDifferential k
              (projectiveSelectedVector k)).toContinuousLinearMap))
        (projectiveUnitReconstruction k 0) := by
      simpa only [projectiveUnitReconstruction_zero] using hab
    have hc := hab'.comp 0 hunit
    convert hc using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro u
      rfl
  have hpi := hasFDerivAt_pi.mpr (fun a =>
    hasFDerivAt_pi.mpr (fun b => hentry a b))
  have heq :
      (projectiveHouseholderFrameDifferential k).toContinuousLinearMap =
        ContinuousLinearMap.pi (fun a => ContinuousLinearMap.pi (fun b =>
          (matrixEntryEvaluationCLM a b).comp
            (projectiveHouseholderFrameDifferential k).toContinuousLinearMap)) := by
    apply ContinuousLinearMap.ext
    intro u
    ext a b
    rfl
  rw [heq]
  exact hpi

/-- Bundled `fderiv` form of the projective Householder computation. -/
theorem fderiv_phaseFixedHouseholderFrame_projective_zero (k : ι) :
    fderiv ℝ (fun z : ProjectiveChartCoordinate k → ℂ =>
      phaseFixedHouseholderFrame k (projectiveUnitReconstruction k z)) 0 =
      (projectiveHouseholderFrameDifferential k).toContinuousLinearMap :=
  (hasFDerivAt_phaseFixedHouseholderFrame_projective_zero k).fderiv

/-- At the chart origin, the Householder-frame differential occupies exactly
the selected row and selected column.  In coordinates it is
`u eₖᴴ + eₖ uᴴ`. -/
theorem projectiveHouseholderFrameDifferential_apply
    (k a b : ι) (u : ProjectiveChartCoordinate k → ℂ) :
    projectiveHouseholderFrameDifferential k u a b =
      (projectiveChartTangentInsertion k u a) *
          (if b = k then 1 else 0) +
        (if a = k then 1 else 0) *
          star (projectiveChartTangentInsertion k u b) := by
  change (phaseFixedHouseholderAlgebraicDifferential k
    (projectiveSelectedVector k) (projectiveChartTangentInsertion k u)) a b = _
  have hsel : projectiveSelectedVector k k = 1 := by
    change projectiveEigenvectorReconstruction k 0 k = 1
    simp
  have hshift (j : ι) :
      phaseFixedHouseholderShift k (projectiveSelectedVector k) j =
        if j = k then 2 else 0 := by
    by_cases hj : j = k
    · subst j
      norm_num [phaseFixedHouseholderShift, hsel, phaseFixedCoordinateVector]
    · simp [phaseFixedHouseholderShift, projectiveSelectedVector,
        projectiveEigenvectorReconstruction, phaseFixedCoordinateVector, hj]
  have huk := projectiveChartTangentInsertion_apply_self k u
  by_cases ha : a = k <;> by_cases hb : b = k
  · subst a
    subst b
    simp [phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      hsel, hshift, huk]
  · subst a
    simp [phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      hsel, hshift, hb, huk]
    norm_num
    ring
  · subst b
    simp [phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      hsel, hshift, ha, huk]
    norm_num
    ring
  · simp [phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      hsel, hshift, ha, hb, huk]

/-- In particular the diagonal entries of the projective frame differential
vanish, as required for a first-order unitary-frame variation. -/
theorem projectiveHouseholderFrameDifferential_apply_diag
    (k a : ι) (u : ProjectiveChartCoordinate k → ℂ) :
    projectiveHouseholderFrameDifferential k u a a = 0 := by
  rw [projectiveHouseholderFrameDifferential_apply]
  by_cases ha : a = k
  · subst a
    simp
  · simp [ha]

end CoareaNative.BlockBand
