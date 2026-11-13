module
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairConjugationDerivative

/-!
# Readback of the coherent eigenpair derivative

This module composes the coherent matrix derivative with selected
Hermitian-coordinate readback.  The resulting derivative is an explicit
continuous-linear composition.  Its final reduction to the canonical gap map
is exactly the remaining pack/unpack extensionality calculation against
`canonicalEigenpairChartAlgebraicDifferential_eq`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

/-- Joint coherent reconstruction read back into selected real Hermitian
coordinates. -/
def coherentSelectedEigenpairDecode {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d → CoherentHermitianCoordinates d :=
  fun x => coherentSelectedMatrixReadbackCLM i
    (coherentEigenpairConjugation i x)

/-- Exact readback derivative, prior to the final algebraic identification. -/
def coherentSelectedEigenpairReadbackDifferential {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedMatrixReadbackCLM i).comp
    (fderiv ℝ (coherentEigenpairConjugation i)
      (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
        CoherentHermitianCoordinates d))

/-- Derivative after coherent selected-coordinate readback. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairReadbackDifferential i E B)
      (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
        CoherentHermitianCoordinates d) := by
  exact (coherentSelectedMatrixReadbackCLM i).hasFDerivAt.comp _
    (hasFDerivAt_coherentEigenpairConjugation_zero i E B)

/-- The readback derivative is uniquely the Fréchet derivative of the coherent
selected decoder. -/
theorem fderiv_coherentSelectedEigenpairDecode_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    fderiv ℝ (coherentSelectedEigenpairDecode i)
        (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
          CoherentHermitianCoordinates d) =
      coherentSelectedEigenpairReadbackDifferential i E B :=
  (hasFDerivAt_coherentSelectedEigenpairDecode_zero i E B).fderiv

end CoareaNative.BlockBand
