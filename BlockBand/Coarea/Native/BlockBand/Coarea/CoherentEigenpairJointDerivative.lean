module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairAnalyticCarriers

/-!
# Coherent packing for the joint eigenpair derivative

This module supplies the continuous-linear packing and readback layer needed
to differentiate the joint reconstruction `H(z) D(E,B) H(z)ᴴ` without using
any of the incompatible `Pi`/`WithLp` instance paths.  Matrix-valued data are
packed through the coherent Euclidean matrix carrier, and selected Hermitian
coordinates are read back through the already verified coordinate functional.

The remaining joint-derivative step is now purely entrywise: apply the product
rule to the finite sums defining `H * D * Hᴴ`, pack those scalar derivatives
with `coherentComplexMatrixEquiv`, and compare the result with
`canonicalEigenpairChartAlgebraicDifferential_eq`.  No further carrier or
continuity construction is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- Continuous-linear wrapping into a coherent finite-dimensional carrier. -/
def coherentCarrierWrapCLM
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    X →L[ℝ] CoherentAnalyticCarrier X :=
  (coherentAnalyticCarrierContinuousLinearEquiv X).symm

/-- Selected coherent Hermitian coordinates, viewed algebraically as canonical
energy/projective/complement block data. -/
def coherentSelectedBlockInputLinearMap {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (selectedEigenpairFinCoordinateLinearEquiv i).toLinearMap.comp
    (coherentAnalyticCarrierLinearEquiv (HermitianCoordinateSpace d)).toLinearMap

/-- The projective component of a selected coherent Hermitian input, with
coherent projective output. -/
def coherentSelectedProjectiveInputCLM {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d →L[ℝ]
      CoherentProjectiveCoordinates
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)) :=
  (coherentCarrierWrapCLM
      (ProjectiveChartCoordinate
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)) → ℂ)).comp
    ((canonicalEigenpairProjectiveInputLinearMap.comp
      (coherentSelectedBlockInputLinearMap i)).toContinuousLinearMap)

/-- The canonical block-diagonal matrix, packed directly into the coherent
matrix carrier. -/
def coherentSelectedBlockDiagonalCLM {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d →L[ℝ]
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) :=
  ((coherentComplexMatrixEquiv (Unit ⊕ Fin (d - 1))).symm :
      Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ →L[ℝ]
        CoherentComplexMatrix (Unit ⊕ Fin (d - 1))).comp
    (matrixLinearMapToContinuous
      (canonicalBlockDiagonalLinearMap.comp
        (coherentSelectedBlockInputLinearMap i)))

/-- Read an arbitrary coherent selected-coordinate matrix back into coherent
real Hermitian coordinates. -/
def coherentSelectedMatrixReadbackCLM {d : ℕ} (i : Fin d) :
    CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) →L[ℝ]
      CoherentHermitianCoordinates d :=
  (coherentCarrierWrapCLM (HermitianCoordinateSpace d)).comp
    ((selectedMatrixFinCoordinateReadCLM i).comp
      ((coherentComplexMatrixEquiv (Unit ⊕ Fin (d - 1))) :
        CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) →L[ℝ]
          Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ))

@[simp] theorem coherentSelectedProjectiveInputCLM_zeroSlice
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    coherentSelectedProjectiveInputCLM i
        (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
          CoherentHermitianCoordinates d) =
      (⟨0⟩ : CoherentProjectiveCoordinates
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1))) := by
  apply congrArg CoherentAnalyticCarrier.mk
  change canonicalProjectiveChartCoordinates
    (((selectedEigenpairFinCoordinateLinearEquiv i)
      ((selectedEigenpairFinCoordinateLinearEquiv i).symm
        (E, ((0 : Fin (d - 1) → ℂ), B)))).2.1) = 0
  rw [(selectedEigenpairFinCoordinateLinearEquiv i).apply_symm_apply]
  exact canonicalProjectiveChartCoordinates_zero

/-- Packing and reading a decoded canonical block matrix recovers exactly the
selected coherent Hermitian coordinate vector. -/
theorem coherentSelectedMatrixReadback_decode
    {d : ℕ} (i : Fin d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    coherentSelectedMatrixReadbackCLM i
        ((coherentComplexMatrixEquiv (Unit ⊕ Fin (d - 1))).symm
          ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm y).1) =
      (⟨(selectedEigenpairFinCoordinateLinearEquiv i).symm y⟩ :
        CoherentHermitianCoordinates d) := by
  apply congrArg CoherentAnalyticCarrier.mk
  exact selectedMatrixFinCoordinateRead_decode i y

/-- The coherent block-diagonal packing is a linear Fréchet map. -/
theorem hasFDerivAt_coherentSelectedBlockDiagonal
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentSelectedBlockDiagonalCLM i)
      (coherentSelectedBlockDiagonalCLM i) x :=
  (coherentSelectedBlockDiagonalCLM i).hasFDerivAt

/-- The coherent projective extraction is a linear Fréchet map. -/
theorem hasFDerivAt_coherentSelectedProjectiveInput
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentSelectedProjectiveInputCLM i)
      (coherentSelectedProjectiveInputCLM i) x :=
  (coherentSelectedProjectiveInputCLM i).hasFDerivAt

end CoareaNative.BlockBand
