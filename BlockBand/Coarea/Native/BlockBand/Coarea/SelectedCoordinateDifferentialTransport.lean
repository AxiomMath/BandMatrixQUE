module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairRealDeterminantTransport

/-!
# Transport of the canonical eigenpair differential through fixed charts

The selected-coordinate split and fixed Householder conjugation are bundled
real-linear equivalences.  Rather than separately choosing orientations and
computing their determinants, we conjugate the canonical block differential by
the complete equivalence.  Determinant invariance under conjugation then shows
that these outer fixed coordinate changes introduce exactly no Jacobian factor.

This is the fixed-point determinant transport used for the nonlinear chart.  The
identification of the derivative of its projective-coordinate parameterization
with the canonical tangent input at the zero slice is
`coherentSelectedEigenpairDerivativeIdentified_of_gap`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Transport the canonical block differential back to Hermitian matrices using
an arbitrary selected coordinate. -/
def selectedCoordinateTransportedDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    RealHermitianMatrix (Fin d) →ₗ[ℝ] RealHermitianMatrix (Fin d) :=
  (selectedCoordinateEigenpairLinearEquiv i).symm.toLinearMap.comp
    ((eigenpairHermitianBlockCoordinateDifferential E B).comp
      (selectedCoordinateEigenpairLinearEquiv i).toLinearMap)

/-- Selected-coordinate transport is conjugation of the canonical
block map by the selected-coordinate equivalence. -/
theorem selectedCoordinateTransportedDifferential_apply
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (A : RealHermitianMatrix (Fin d)) :
    selectedCoordinateTransportedDifferential i E B A =
      (selectedCoordinateEigenpairLinearEquiv i).symm
        (eigenpairHermitianBlockCoordinateDifferential E B
          (selectedCoordinateEigenpairLinearEquiv i A)) := by
  rfl

/-- Conjugating by the selected-coordinate equivalence preserves the complete
real determinant exactly. -/
theorem det_selectedCoordinateTransportedDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    LinearMap.det (selectedCoordinateTransportedDifferential i E B) =
      eigenpairLocalRealJacobianDensity E B := by
  rw [selectedCoordinateTransportedDifferential]
  calc
    LinearMap.det
        ((selectedCoordinateEigenpairLinearEquiv i).symm.toLinearMap.comp
          ((eigenpairHermitianBlockCoordinateDifferential E B).comp
            (selectedCoordinateEigenpairLinearEquiv i).toLinearMap)) =
      LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B) := by
        simpa using LinearMap.det_conj
          (eigenpairHermitianBlockCoordinateDifferential E B)
          (selectedCoordinateEigenpairLinearEquiv i).symm
    _ = eigenpairLocalRealJacobianDensity E B :=
      det_eigenpairHermitianBlockCoordinateDifferential E B

/-- The absolute determinant is likewise the canonical nonnegative density. -/
theorem abs_det_selectedCoordinateTransportedDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    |LinearMap.det (selectedCoordinateTransportedDifferential i E B)| =
      eigenpairLocalRealJacobianDensity E B := by
  rw [det_selectedCoordinateTransportedDifferential]
  exact abs_of_nonneg (eigenpairOffdiagJacobian_nonneg E B)

/-- Transport the canonical block differential through the complete fixed
ordered-eigenline equivalence.  This single equivalence includes both unitary
Householder conjugation and selected-coordinate reindexing/block splitting. -/
def orderedEigenlineTransportedDifferential
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (E : ℝ) (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    RealHermitianMatrix (Fin d) →ₗ[ℝ] RealHermitianMatrix (Fin d) :=
  (orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm.toLinearMap.comp
    ((eigenpairHermitianBlockCoordinateDifferential E B).comp
      (orderedEigenlineSelectedCoordinateLinearEquiv r p x).toLinearMap)

/-- The complete fixed-frame transport acts by encoding, applying the canonical
block differential, and decoding. -/
theorem orderedEigenlineTransportedDifferential_apply
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (E : ℝ) (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (A : RealHermitianMatrix (Fin d)) :
    orderedEigenlineTransportedDifferential r p x E B A =
      (orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm
        (eigenpairHermitianBlockCoordinateDifferential E B
          (orderedEigenlineSelectedCoordinateLinearEquiv r p x A)) := by
  rfl

/-- Neither fixed unitary conjugation nor selected-coordinate reindexing adds a
Jacobian factor: their combined transport preserves the canonical determinant. -/
theorem det_orderedEigenlineTransportedDifferential
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (E : ℝ) (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    LinearMap.det (orderedEigenlineTransportedDifferential r p x E B) =
      eigenpairLocalRealJacobianDensity E B := by
  rw [orderedEigenlineTransportedDifferential]
  calc
    LinearMap.det
        ((orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm.toLinearMap.comp
          ((eigenpairHermitianBlockCoordinateDifferential E B).comp
            (orderedEigenlineSelectedCoordinateLinearEquiv r p x).toLinearMap)) =
      LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B) := by
        simpa using LinearMap.det_conj
          (eigenpairHermitianBlockCoordinateDifferential E B)
          (orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm
    _ = eigenpairLocalRealJacobianDensity E B :=
      det_eigenpairHermitianBlockCoordinateDifferential E B

/-- Absolute-determinant form used directly by Mathlib's real Jacobian
change-of-variables theorem. -/
theorem abs_det_orderedEigenlineTransportedDifferential
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (E : ℝ) (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    |LinearMap.det (orderedEigenlineTransportedDifferential r p x E B)| =
      eigenpairLocalRealJacobianDensity E B := by
  rw [det_orderedEigenlineTransportedDifferential]
  exact abs_of_nonneg (eigenpairOffdiagJacobian_nonneg E B)

end CoareaNative.BlockBand
