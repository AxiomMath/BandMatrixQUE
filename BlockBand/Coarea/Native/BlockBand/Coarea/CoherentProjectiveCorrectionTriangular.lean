module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionBlockDeterminant
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairIncidenceChangeOfVariables

/-!
# Block-diagonal model for the coherent projective correction

The arbitrary-coordinate calculation has one non-identity diagonal block: the
real normalized affine tangent block.  This module places that block in the
energy/projective/complement coordinate carrier, proves the two other
diagonal blocks contribute determinant one, and transports the result to the
coherent carrier by the selected-coordinate linear equivalence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

/-- The diagonal part of the projective correction in selected block
coordinates.  Energy and the complementary Hermitian matrix are fixed, while
the projective coordinate receives the normalized rank-one tangent map. -/
def coherentProjectiveCorrectionBlockDiagonal {d : ℕ} (z : Fin (d - 1) → ℂ) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  LinearMap.prodMap LinearMap.id
    (LinearMap.prodMap (projectiveNormalizedTangentBlock z) LinearMap.id)

@[simp] theorem coherentProjectiveCorrectionBlockDiagonal_apply {d : ℕ}
    (z : Fin (d - 1) → ℂ)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    coherentProjectiveCorrectionBlockDiagonal z ξ =
      (ξ.1, (projectiveNormalizedTangentBlock z ξ.2.1, ξ.2.2)) := by
  rfl

/-- The determinant of the block-diagonal correction is precisely the
normalized projective determinant; both remaining diagonal blocks are
identities. -/
theorem det_coherentProjectiveCorrectionBlockDiagonal {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    LinearMap.det (coherentProjectiveCorrectionBlockDiagonal z) =
      LinearMap.det (projectiveNormalizedTangentBlock z) := by
  rw [coherentProjectiveCorrectionBlockDiagonal, LinearMap.det_prodMap,
    LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_id, one_mul, mul_one]

/-- The selected-coordinate diagonal model has the exact affine-projective
density. -/
theorem abs_det_coherentProjectiveCorrectionBlockDiagonal {d : ℕ}
    (i : Fin d) (z : Fin (d - 1) → ℂ) :
    |LinearMap.det (coherentProjectiveCorrectionBlockDiagonal z)| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d := by
  rw [det_coherentProjectiveCorrectionBlockDiagonal]
  exact abs_det_projectiveNormalizedTangentBlock i z

/-- Transport of the diagonal correction model to the coherent Hermitian
carrier. -/
def coherentProjectiveCorrectionDiagonalModel {d : ℕ} (i : Fin d)
    (z : Fin (d - 1) → ℂ) :
    CoherentHermitianCoordinates d →ₗ[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedBlockCoordinateLinearEquiv i).symm.toLinearMap.comp
    ((coherentProjectiveCorrectionBlockDiagonal z).comp
      (coherentSelectedBlockCoordinateLinearEquiv i).toLinearMap)

/-- Conjugation by selected coherent coordinates preserves the determinant of
the projective diagonal model. -/
theorem det_coherentProjectiveCorrectionDiagonalModel {d : ℕ} (i : Fin d)
    (z : Fin (d - 1) → ℂ) :
    LinearMap.det (coherentProjectiveCorrectionDiagonalModel i z) =
      LinearMap.det (coherentProjectiveCorrectionBlockDiagonal z) := by
  exact LinearMap.det_conj (coherentProjectiveCorrectionBlockDiagonal z)
    (coherentSelectedBlockCoordinateLinearEquiv i).symm

/-- Exact determinant of the coherent diagonal model. -/
theorem abs_det_coherentProjectiveCorrectionDiagonalModel {d : ℕ}
    (i : Fin d) (z : Fin (d - 1) → ℂ) :
    |LinearMap.det (coherentProjectiveCorrectionDiagonalModel i z)| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d := by
  rw [det_coherentProjectiveCorrectionDiagonalModel,
    abs_det_coherentProjectiveCorrectionBlockDiagonal i z]

/-- Composing the verified gap differential with the coherent diagonal model
already gives the paper's bare projective-density-times-gap determinant.
The only remaining identification for the nonlinear decoder is that its
explicit correction differs from this model by unit-diagonal shears. -/
theorem abs_det_gap_comp_coherentProjectiveCorrectionDiagonalModel {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det ((coherentEigenpairGapDifferential i E B).comp
      (coherentProjectiveCorrectionDiagonalModel i z))| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d *
        Complex.normSq (eigenpairGapMatrix E B.1).det := by
  rw [LinearMap.det_comp, abs_mul,
    abs_det_coherentEigenpairGapDifferential,
    abs_det_coherentProjectiveCorrectionDiagonalModel,
    eigenpairLocalRealJacobianDensity_eq_normSq_det]
  ring

/-- The projective-Jacobian defect of the verified diagonal model is one. -/
theorem coherentProjectiveCorrectionDiagonalModel_defect_eq_one {d : ℕ}
    (i : Fin d) (z : Fin (d - 1) → ℂ) :
    (((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d)⁻¹ *
      |LinearMap.det (coherentProjectiveCorrectionDiagonalModel i z)| = 1 := by
  rw [abs_det_coherentProjectiveCorrectionDiagonalModel]
  have hsum : 0 ≤ ∑ j, Complex.normSq (z j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j)
  have hne : ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d ≠ 0 := by
    apply pow_ne_zero
    exact inv_ne_zero (by linarith)
  exact inv_mul_cancel₀ hne

end CoareaNative.BlockBand
