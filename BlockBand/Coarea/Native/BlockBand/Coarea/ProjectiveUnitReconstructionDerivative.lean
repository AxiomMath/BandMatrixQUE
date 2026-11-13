module

public import BlockBand.Coarea.Native.BlockBand.Coarea.SelectedCoordinateDifferentialTransport
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Derivative of the phase-fixed projective unit reconstruction

This module computes the real Fréchet derivative of the affine
projective representative and its unit normalization.  The base-point formula
at the origin of a selected chart is the complementary-coordinate insertion;
this is the canonical tangent variation used by the eigenpair Jacobian.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Insert a projective-chart tangent vector in the complementary coordinates,
with zero in the distinguished coordinate. -/
def projectiveChartTangentInsertion (k : ι) :
    (ProjectiveChartCoordinate k → ℂ) →ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 fun i => if h : i = k then 0 else u ⟨i, h⟩
  map_add' u v := by
    apply PiLp.ext
    intro i
    by_cases hi : i = k <;> simp [hi]
  map_smul' c u := by
    apply PiLp.ext
    intro i
    by_cases hi : i = k <;> simp [hi]

@[simp] theorem projectiveChartTangentInsertion_apply_self (k : ι)
    (u : ProjectiveChartCoordinate k → ℂ) :
    projectiveChartTangentInsertion k u k = 0 := by
  simp [projectiveChartTangentInsertion]

@[simp] theorem projectiveChartTangentInsertion_apply (k : ι)
    (u : ProjectiveChartCoordinate k → ℂ) (j : ProjectiveChartCoordinate k) :
    projectiveChartTangentInsertion k u j.1 = u j := by
  simp [projectiveChartTangentInsertion, j.property]

/-- The selected basis vector of the affine chart. -/
def projectiveSelectedVector (k : ι) : EuclideanSpace ℂ ι :=
  projectiveEigenvectorReconstruction k 0

/-- Affine projective reconstruction is the selected basis vector plus tangent
insertion. -/
theorem projectiveEigenvectorReconstruction_eq_add_tangent (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveEigenvectorReconstruction k z =
      projectiveSelectedVector k + projectiveChartTangentInsertion k z := by
  ext i
  by_cases hi : i = k
  · subst i
    simp [projectiveSelectedVector]
  · simp [projectiveSelectedVector, projectiveEigenvectorReconstruction,
      projectiveChartTangentInsertion, hi]

/-- The affine reconstruction has the constant complementary-coordinate
insertion as its real Fréchet derivative. -/
theorem hasFDerivAt_projectiveEigenvectorReconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    HasFDerivAt (projectiveEigenvectorReconstruction k)
      (projectiveChartTangentInsertion k).toContinuousLinearMap z := by
  rw [show projectiveEigenvectorReconstruction k = fun w =>
      projectiveSelectedVector k + projectiveChartTangentInsertion k w by
    funext w
    exact projectiveEigenvectorReconstruction_eq_add_tangent k w]
  convert (hasFDerivAt_const (projectiveSelectedVector k) z).add
    (projectiveChartTangentInsertion k).toContinuousLinearMap.hasFDerivAt using 1
  · funext w
    rfl
  · simp

/-- The selected chart vector has Euclidean norm one. -/
@[simp] theorem norm_projectiveSelectedVector (k : ι) :
    ‖projectiveSelectedVector k‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [projectiveSelectedVector, projectiveEigenvectorReconstruction]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [hbk]
  · simp

/-- The phase-fixed unit reconstruction agrees with the selected basis vector
at the chart origin. -/
@[simp] theorem projectiveUnitReconstruction_zero (k : ι) :
    projectiveUnitReconstruction k 0 = projectiveSelectedVector k := by
  rw [projectiveUnitReconstruction, show
    projectiveEigenvectorReconstruction k 0 = projectiveSelectedVector k from rfl,
    norm_projectiveSelectedVector]
  simp

/-- Tangent insertion is real-orthogonal to the selected coordinate vector. -/
theorem inner_projectiveSelectedVector_tangentInsertion (k : ι)
    (u : ProjectiveChartCoordinate k → ℂ) :
    inner ℝ (projectiveSelectedVector k)
      (projectiveChartTangentInsertion k u) = 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_zero]
  intro i hi
  by_cases hik : i = k
  · subst i
    simp
  · simp [projectiveSelectedVector, projectiveEigenvectorReconstruction,
      projectiveChartTangentInsertion, hik]

/-- The norm of affine reconstruction has zero derivative at the chart origin. -/
theorem hasFDerivAt_norm_projectiveEigenvectorReconstruction_zero (k : ι) :
    HasFDerivAt (fun z : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k z‖)
      (0 : (ProjectiveChartCoordinate k → ℂ) →L[ℝ] ℝ) 0 := by
  have hrec := hasFDerivAt_projectiveEigenvectorReconstruction k
    (0 : ProjectiveChartCoordinate k → ℂ)
  have hsq := hrec.norm_sq
  have hsq0 : HasFDerivAt (fun z : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k z‖ ^ 2)
      (0 : (ProjectiveChartCoordinate k → ℂ) →L[ℝ] ℝ) 0 := by
    convert hsq using 1
    ext u
    simp only [zero_apply, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [show projectiveEigenvectorReconstruction k 0 =
      projectiveSelectedVector k from rfl,
      show (projectiveChartTangentInsertion k).toContinuousLinearMap u =
        projectiveChartTangentInsertion k u from rfl,
      inner_projectiveSelectedVector_tangentInsertion]
    simp
  have hsqrt := hsq0.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (projectiveEigenvectorReconstruction_ne_zero k 0)))
  convert hsqrt using 1
  · funext z
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp

/-- The normalization scalar has zero derivative at the origin of a selected
projective chart. -/
theorem hasFDerivAt_inv_norm_projectiveEigenvectorReconstruction_zero (k : ι) :
    HasFDerivAt (fun z : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k z‖⁻¹)
      (0 : (ProjectiveChartCoordinate k → ℂ) →L[ℝ] ℝ) 0 := by
  have hnorm := hasFDerivAt_norm_projectiveEigenvectorReconstruction_zero k
  have hne : ‖projectiveEigenvectorReconstruction k
      (0 : ProjectiveChartCoordinate k → ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (projectiveEigenvectorReconstruction_ne_zero k 0)
  convert (hasFDerivAt_inv hne).comp 0 hnorm using 1
  · rfl
  · ext u
    simp

/-- At the canonical affine-chart origin the derivative of phase-fixed unit
reconstruction is exactly complementary-coordinate insertion. -/
theorem hasFDerivAt_projectiveUnitReconstruction_zero (k : ι) :
    HasFDerivAt (projectiveUnitReconstruction k)
      (projectiveChartTangentInsertion k).toContinuousLinearMap 0 := by
  have hs := hasFDerivAt_inv_norm_projectiveEigenvectorReconstruction_zero k
  have hr := hasFDerivAt_projectiveEigenvectorReconstruction k
    (0 : ProjectiveChartCoordinate k → ℂ)
  change HasFDerivAt (fun z : ProjectiveChartCoordinate k → ℂ =>
    ‖projectiveEigenvectorReconstruction k z‖⁻¹ •
      projectiveEigenvectorReconstruction k z) _ 0
  convert hs.smul hr using 1
  ext u i
  rw [show projectiveEigenvectorReconstruction k 0 = projectiveSelectedVector k from rfl,
    norm_projectiveSelectedVector]
  simp

/-- Bundled derivative form of the canonical chart-origin computation. -/
theorem fderiv_projectiveUnitReconstruction_zero (k : ι) :
    fderiv ℝ (projectiveUnitReconstruction k) 0 =
      (projectiveChartTangentInsertion k).toContinuousLinearMap :=
  (hasFDerivAt_projectiveUnitReconstruction_zero k).fderiv

end CoareaNative.BlockBand
