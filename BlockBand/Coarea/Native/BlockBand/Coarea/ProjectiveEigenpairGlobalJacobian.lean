module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairLocalJacobian
public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveUnitReconstructionSmooth

/-!
# Global affine-projective eigenpair Jacobian

The zero-projective slice contributes the squared spectral-gap determinant, but
that determinant alone is not the Jacobian of the nonlinear phase-fixed chart
away from the slice.  In an affine chart with representative `(1,z)`, the
projective volume density is

`(1 + ∑ j, ‖z j‖²) ^ (-d)`

where `d` is the ambient complex dimension.  This module records that factor
intrinsically as the `2d`-th power of the selected coordinate of the normalized
representative, combines it with the gap determinant, and proves the exact
determinant-composition lemma used to transfer an arbitrary-point derivative
computation.

The declarations here do **not** identify the Fréchet derivative of the nonlinear
decoder at arbitrary `z`.  For the coherent selected decoder, the factorization of
that derivative into the zero-slice gap block and a
projective correction whose absolute real determinant is the density defined below
is `fderiv_coherentSelectedEigenpairDecode_factorization` with
`abs_det_coherentEigenpairProjectiveCorrection`; the resulting global Jacobian is
`abs_det_fderiv_coherentSelectedEigenpairDecode_globalInput`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared radius of the affine representative `(1,z)` in a chart. -/
def projectiveAffineRadiusSq (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) : ℝ :=
  1 + ∑ j, Complex.normSq (z j)

/-- The affine representative has squared Euclidean norm
`1 + ∑ j, ‖z j‖²`. -/
theorem norm_projectiveEigenvectorReconstruction_sq (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    ‖projectiveEigenvectorReconstruction k z‖ ^ 2 =
      projectiveAffineRadiusSq k z := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · let f : ι → ℝ := fun i =>
      ‖projectiveEigenvectorReconstruction k z i‖ ^ 2
    have hsplit : (∑ i, f i) = (∑ i ∈ Finset.univ.erase k, f i) + f k := by
      exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)).symm
    have hcomp : (∑ i ∈ Finset.univ.erase k, f i) =
        ∑ j : ProjectiveChartCoordinate k, f j.1 := by
      apply Finset.sum_subtype
      intro i
      simp
    rw [hsplit, hcomp]
    simp [f, projectiveEigenvectorReconstruction_apply,
      Complex.sq_norm, add_comm, projectiveAffineRadiusSq]
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Away from the affine origin, the squared radius is strictly larger than
one.  In particular the global projective correction cannot be silently
replaced by its zero-slice value. -/
theorem one_lt_projectiveAffineRadiusSq_of_ne_zero (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) (hz : z ≠ 0) :
    1 < projectiveAffineRadiusSq k z := by
  have hex : ∃ j, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  obtain ⟨j, hj⟩ := hex
  have hjpos : 0 < Complex.normSq (z j) :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm fun h => hj (Complex.normSq_eq_zero.mp h))
  have hjle : Complex.normSq (z j) ≤ ∑ a, Complex.normSq (z a) := by
    exact Finset.single_le_sum (fun a _ => Complex.normSq_nonneg (z a))
      (Finset.mem_univ j)
  unfold projectiveAffineRadiusSq
  linarith

/-- The projective affine-chart density in ambient complex dimension `card ι`.
It is one at the chart origin and is nonconstant away from it. -/
def projectiveAffineDensity (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) : ℝ :=
  (projectiveAffineRadiusSq k z)⁻¹ ^ Fintype.card ι

/-- Intrinsic form of the projective density: it is the `2d`-th power of
the positive selected coordinate of the phase-fixed unit representative. -/
theorem projectiveAffineDensity_eq_selected_re_pow (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveAffineDensity k z =
      (projectiveUnitReconstruction k z k).re ^ (2 * Fintype.card ι) := by
  rw [projectiveUnitReconstruction_apply_self]
  simp only [Complex.ofReal_re, projectiveAffineDensity]
  rw [← norm_projectiveEigenvectorReconstruction_sq k z]
  rw [inv_pow]
  rw [← pow_mul]
  simp [Nat.mul_comm]

/-- The projective correction is normalized to one at the zero slice. -/
@[simp] theorem projectiveAffineDensity_zero (k : ι) :
    projectiveAffineDensity k 0 = 1 := by
  simp [projectiveAffineDensity, projectiveAffineRadiusSq]

/-- Correct candidate for the absolute real Jacobian density of the nonlinear
phase-fixed decoder at arbitrary affine projective coordinate `z`: projective
volume density times the zero-slice squared-gap density.  The name `Density`
(rather than a determinant theorem) is deliberate until the arbitrary-point
Fréchet derivative is factored. -/
def projectiveEigenpairGlobalJacobianDensity (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) (E : ℝ)
    (B : Matrix (ProjectiveChartCoordinate k)
      (ProjectiveChartCoordinate k) ℂ) : ℝ :=
  projectiveAffineDensity k z * eigenpairLocalRealJacobianDensity E B

/-- Exact arbitrary-coordinate formula: the extra factor relative to the
zero slice is `(1 + ∑ ‖z_j‖²)⁻ᵈ`. -/
theorem projectiveEigenpairGlobalJacobianDensity_eq (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) (E : ℝ)
    (B : Matrix (ProjectiveChartCoordinate k)
      (ProjectiveChartCoordinate k) ℂ) :
    projectiveEigenpairGlobalJacobianDensity k z E B =
      (projectiveAffineRadiusSq k z)⁻¹ ^ Fintype.card ι *
        Complex.normSq (eigenpairGapMatrix E B).det := by
  rw [projectiveEigenpairGlobalJacobianDensity, projectiveAffineDensity,
    eigenpairLocalRealJacobianDensity_eq_normSq_det]

/-- For a Hermitian complementary block, the global density is the projective
factor times the real squared spectral-gap determinant. -/
theorem projectiveEigenpairGlobalJacobianDensity_eq_gap_sq (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) (E : ℝ)
    {B : Matrix (ProjectiveChartCoordinate k)
      (ProjectiveChartCoordinate k) ℂ} (hB : B.IsHermitian) :
    projectiveEigenpairGlobalJacobianDensity k z E B =
      (projectiveAffineRadiusSq k z)⁻¹ ^ Fintype.card ι *
        (eigenpairGapMatrix E B).det.re ^ 2 := by
  rw [projectiveEigenpairGlobalJacobianDensity, projectiveAffineDensity,
    eigenpairLocalRealJacobianDensity_eq_detGap_sq E hB]

/-- At the affine origin the global density reduces to the previously
proved zero-slice density. -/
@[simp] theorem projectiveEigenpairGlobalJacobianDensity_zero (k : ι)
    (E : ℝ)
    (B : Matrix (ProjectiveChartCoordinate k)
      (ProjectiveChartCoordinate k) ℂ) :
    projectiveEigenpairGlobalJacobianDensity k 0 E B =
      eigenpairLocalRealJacobianDensity E B := by
  simp [projectiveEigenpairGlobalJacobianDensity]

/-- Determinant transfer at arbitrary projective coordinate.

If the coordinate differential factors
as the zero-slice energy/gap/complement differential followed by a
projective correction, and the correction has the expected absolute
determinant, multiplicativity gives the full global formula.  These are the
hypotheses `hfactor` and `hprojective`. -/
theorem abs_det_eq_projectiveEigenpairGlobalJacobianDensity_of_factorization
    (k : ι) (z : ProjectiveChartCoordinate k → ℂ) (E : ℝ)
    (B : RealHermitianMatrix (ProjectiveChartCoordinate k))
    (L P : EigenpairHermitianBlockCoordinates (ProjectiveChartCoordinate k) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (ProjectiveChartCoordinate k))
    (hfactor : L =
      (eigenpairHermitianBlockCoordinateDifferential E B.1).comp P)
    (hprojective : |LinearMap.det P| = projectiveAffineDensity k z) :
    |LinearMap.det L| =
      projectiveEigenpairGlobalJacobianDensity k z E B.1 := by
  rw [hfactor, LinearMap.det_comp, abs_mul,
    abs_det_eigenpairHermitianBlockCoordinateDifferential,
    hprojective, projectiveEigenpairGlobalJacobianDensity]
  ring

end CoareaNative.BlockBand
