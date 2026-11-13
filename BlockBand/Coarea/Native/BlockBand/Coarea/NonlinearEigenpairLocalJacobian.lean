module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairChartDerivative
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Nondegenerate local Jacobian of the nonlinear eigenpair chart

This module packages the exact Jacobian and nondegeneracy consequences of the
joint algebraic differential already identified for the nonlinear phase-fixed
eigenpair decoder.  At the zero-projective slice, the energy and complementary
Hermitian blocks are unchanged, while the projective tangent block is the real
linearization of `E I - B`.  Hence the full real determinant is the squared
complex gap determinant, and a nonzero gap determinant makes the differential
a real-linear (indeed continuous-linear) equivalence.

These are precisely the pointwise hypotheses needed by a finite-dimensional
inverse-function/change-of-variables argument.  This module does not claim a
local diffeomorphism: that conclusion additionally needs the Fréchet
derivative of the *joint nonlinear decoder* together with continuity of that
derivative on a neighborhood.  For the coherent decoder these are
`hasFDerivAt_coherentSelectedEigenpairDecode` and
`contDiff_coherentSelectedEigenpairDecode`, and the local inverse is
`coherentSelectedEigenpairLocalHomeomorph`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The determinant of the selected-coordinate algebraic differential is the
canonical local real eigenpair Jacobian density.  The selected coordinate does
not introduce an orientation or volume factor. -/
theorem det_selectedEigenpairCoordinateChartAlgebraicDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    LinearMap.det
        (selectedEigenpairCoordinateChartAlgebraicDifferential i E B) =
      eigenpairLocalRealJacobianDensity E B.1 := by
  exact det_eigenpairHermitianBlockCoordinateDifferential E B.1

/-- Absolute-determinant form required by Mathlib's Jacobian
change-of-variables theorem. -/
theorem abs_det_selectedEigenpairCoordinateChartAlgebraicDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det
        (selectedEigenpairCoordinateChartAlgebraicDifferential i E B)| =
      eigenpairLocalRealJacobianDensity E B.1 := by
  rw [det_selectedEigenpairCoordinateChartAlgebraicDifferential]
  exact abs_of_nonneg (eigenpairOffdiagJacobian_nonneg E B.1)

/-- The algebraic differential is nonsingular exactly when the complex gap
matrix has nonzero determinant. -/
theorem det_selectedEigenpairCoordinateChartAlgebraicDifferential_ne_zero_iff
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    LinearMap.det
        (selectedEigenpairCoordinateChartAlgebraicDifferential i E B) ≠ 0 ↔
      (eigenpairGapMatrix E B.1).det ≠ 0 := by
  rw [det_selectedEigenpairCoordinateChartAlgebraicDifferential,
    eigenpairLocalRealJacobianDensity_eq_normSq_det]
  constructor
  · intro hnorm hdet
    apply hnorm
    rw [hdet, Complex.normSq_zero]
  · intro hdet hnorm
    exact hdet (Complex.normSq_eq_zero.mp hnorm)

/-- The local density is strictly positive exactly off the complementary
spectrum, expressed as nonvanishing of `det (E I - B)`. -/
theorem eigenpairLocalRealJacobianDensity_pos_iff_gap_det_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    0 < eigenpairLocalRealJacobianDensity E B ↔
      (eigenpairGapMatrix E B).det ≠ 0 := by
  rw [eigenpairLocalRealJacobianDensity_eq_normSq_det]
  constructor
  · intro h hdet
    rw [hdet, Complex.normSq_zero] at h
    exact (lt_irrefl 0) h
  · intro hdet
    exact lt_of_le_of_ne (Complex.normSq_nonneg _)
      (Ne.symm fun hzero => hdet (Complex.normSq_eq_zero.mp hzero))

/-- When the selected energy is outside the complementary spectrum, the exact
algebraic differential is a real-linear automorphism. -/
def selectedEigenpairCoordinateChartAlgebraicLinearEquiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (selectedEigenpairCoordinateChartAlgebraicDifferential i E B).equivOfDetNeZero
    ((det_selectedEigenpairCoordinateChartAlgebraicDifferential_ne_zero_iff
      i E B).2 hgap)

/-- The automorphism constructed from the nonzero determinant acts exactly as
the algebraic differential. -/
theorem selectedEigenpairCoordinateChartAlgebraicLinearEquiv_apply
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedEigenpairCoordinateChartAlgebraicLinearEquiv i E B hgap ξ =
      selectedEigenpairCoordinateChartAlgebraicDifferential i E B ξ := by
  rfl

/-- The same nonsingular differential as a continuous real-linear
equivalence, the exact derivative object expected by the inverse function
theorem in finite dimension. -/
def selectedEigenpairCoordinateChartAlgebraicContinuousLinearEquiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) ≃L[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (selectedEigenpairCoordinateChartAlgebraicLinearEquiv i E B hgap).toContinuousLinearEquiv

/-- Paper-facing zero-slice local data: the nonlinear coordinate decoder fixes
its base point and its identified joint algebraic differential has exactly the
squared-gap absolute Jacobian density. -/
theorem selectedEigenpairCoordinateChart_zeroSlice_value_and_jacobian
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    selectedEigenpairCoordinateChartDecode i
        (E, ((0 : Fin (d - 1) → ℂ), B)) =
        (E, ((0 : Fin (d - 1) → ℂ), B)) ∧
      |LinearMap.det
          (selectedEigenpairCoordinateChartAlgebraicDifferential i E B)| =
        Complex.normSq (eigenpairGapMatrix E B.1).det := by
  constructor
  · exact selectedEigenpairCoordinateChartDecode_zero_tangent i E B
  · rw [abs_det_selectedEigenpairCoordinateChartAlgebraicDifferential,
      eigenpairLocalRealJacobianDensity_eq_normSq_det]

/-- For a Hermitian complementary block, the same zero-slice Jacobian is the
paper's real squared gap determinant `det(E I - B)^2`. -/
theorem abs_det_selectedEigenpairCoordinateChartAlgebraicDifferential_eq_gap_sq
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det
        (selectedEigenpairCoordinateChartAlgebraicDifferential i E B)| =
      (eigenpairGapMatrix E B.1).det.re ^ 2 := by
  rw [abs_det_selectedEigenpairCoordinateChartAlgebraicDifferential,
    eigenpairLocalRealJacobianDensity_eq_detGap_sq E B.2]

end CoareaNative.BlockBand
