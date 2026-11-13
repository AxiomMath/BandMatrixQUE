module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveUnitReconstructionSmooth

/-!
# Global smoothness of the coherent projective Householder chart

The affine representative of a projective eigenline never meets the pole of the
phase-fixed Householder formula.  Consequently every matrix entry, and the
matrix packed in the coherent Euclidean carrier, has a real Fréchet
derivative at every affine projective coordinate.  The differentials below are
continuous-linear maps assembled only from coherent carriers; in particular no
choice between the competing finite-`Pi`/`PiLp` module structures is exposed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The global entry differential is the algebraic Householder entry
differential composed with the derivative of normalized affine
reconstruction. -/
def coherentProjectiveHouseholderFrameEntryDifferentialAt
    (k a b : ι) (z : CoherentProjectiveCoordinates k) :
    CoherentProjectiveCoordinates k →L[ℝ] ℂ :=
  (coherentPhaseFixedHouseholderFrameEntryDifferential k a b
      (coherentProjectiveUnitReconstruction k z)).comp
    (fderiv ℝ (coherentProjectiveUnitReconstruction k) z)

/-- Every entry of the coherent projective Householder frame has the explicit
chain-rule Fréchet derivative at every affine coordinate. -/
theorem hasFDerivAt_coherentProjectiveHouseholderFrameEntry
    (k a b : ι) (z : CoherentProjectiveCoordinates k) :
    HasFDerivAt
      (fun w : CoherentProjectiveCoordinates k =>
        coherentProjectiveHouseholderFrame k w a b)
      (coherentProjectiveHouseholderFrameEntryDifferentialAt k a b z) z := by
  have hu := (differentiableAt_coherentProjectiveUnitReconstruction k z).hasFDerivAt
  have hden :
      1 + ((coherentProjectiveUnitReconstruction k z).value k).re ≠ 0 := by
    change 1 + (projectiveUnitReconstruction k z.value k).re ≠ 0
    have hpos := projectiveUnitReconstruction_self_re_pos k z.value
    linarith
  exact (hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry
    k a b (coherentProjectiveUnitReconstruction k z) hden).comp z hu

/-- The entrywise continuous-linear differential of the entire matrix. -/
def coherentProjectiveHouseholderFrameDifferentialAt
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    CoherentProjectiveCoordinates k →L[ℝ] Matrix ι ι ℂ :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
    coherentProjectiveHouseholderFrameEntryDifferentialAt k a b z

/-- The unpacked matrix-valued coherent projective Householder frame has the
entrywise assembled Fréchet derivative at every affine coordinate. -/
theorem hasFDerivAt_coherentProjectiveHouseholderFrame
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    HasFDerivAt (coherentProjectiveHouseholderFrame k)
      (coherentProjectiveHouseholderFrameDifferentialAt k z) z := by
  exact hasFDerivAt_pi.mpr fun a => hasFDerivAt_pi.mpr fun b =>
    hasFDerivAt_coherentProjectiveHouseholderFrameEntry k a b z

/-- Pack the global matrix differential into the coherent Euclidean matrix
carrier.  This is the continuous-linear interface for downstream chart and
Jacobian computations. -/
def coherentProjectiveHouseholderEuclideanDifferentialAt
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    CoherentProjectiveCoordinates k →L[ℝ] EuclideanSpace ℂ (ι × ι) :=
  ((LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv (ι × ι) ℂ).symm.toLinearEquiv.restrictScalars ℝ)) :
    ((ι × ι) → ℂ) ≃L[ℝ] EuclideanSpace ℂ (ι × ι)).toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun ij =>
        coherentProjectiveHouseholderFrameEntryDifferentialAt
          k ij.1 ij.2 z)

/-- The Euclidean packing of all Householder entries has the assembled global
Fréchet derivative. -/
theorem hasFDerivAt_coherentProjectiveHouseholderEuclidean
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    HasFDerivAt (coherentProjectiveHouseholderEuclidean k)
      (coherentProjectiveHouseholderEuclideanDifferentialAt k z) z := by
  have hfun : HasFDerivAt
      (fun w : CoherentProjectiveCoordinates k => fun ij : ι × ι =>
        coherentProjectiveHouseholderFrame k w ij.1 ij.2)
      (ContinuousLinearMap.pi fun ij : ι × ι =>
        coherentProjectiveHouseholderFrameEntryDifferentialAt
          k ij.1 ij.2 z) z :=
    hasFDerivAt_pi.mpr fun ij =>
      hasFDerivAt_coherentProjectiveHouseholderFrameEntry k ij.1 ij.2 z
  let eR : EuclideanSpace ℂ (ι × ι) ≃L[ℝ] ((ι × ι) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv (ι × ι) ℂ).toLinearEquiv.restrictScalars ℝ)
  apply (eR.comp_hasFDerivAt_iff).mp
  convert hfun using 1
  · funext w ij
    rfl
  · apply ContinuousLinearMap.ext
    intro u
    rfl

/-- Pack the global Euclidean differential into the coherent matrix carrier.
This is the continuous-linear interface for downstream chart and Jacobian
computations. -/
def coherentProjectiveHouseholderMatrixDifferentialAt
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    CoherentProjectiveCoordinates k →L[ℝ] CoherentComplexMatrix ι :=
  let T : CoherentProjectiveCoordinates k →ₗ[ℝ] CoherentComplexMatrix ι :=
    { toFun := fun u =>
        ⟨coherentProjectiveHouseholderEuclideanDifferentialAt k z u⟩
      map_add' := by
        intro u v
        congr 1
        exact (coherentProjectiveHouseholderEuclideanDifferentialAt k z).map_add u v
      map_smul' := by
        intro c u
        congr 1
        exact (coherentProjectiveHouseholderEuclideanDifferentialAt k z).map_smul c u }
  T.toContinuousLinearMap

/-- The coherently packed Householder matrix has its Fréchet derivative
at every affine projective coordinate. -/
theorem hasFDerivAt_coherentProjectiveHouseholderMatrix
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    HasFDerivAt (coherentProjectiveHouseholderMatrix k)
      (coherentProjectiveHouseholderMatrixDifferentialAt k z) z := by
  convert HasFDerivAt.coherentOutput
    (hasFDerivAt_coherentProjectiveHouseholderEuclidean k z) using 1
  · rfl
  · rfl

/-- The bundled Fréchet derivative of the packed coherent matrix is exactly the
entrywise continuous-linear map constructed above. -/
theorem fderiv_coherentProjectiveHouseholderMatrix
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    fderiv ℝ (coherentProjectiveHouseholderMatrix k) z =
      coherentProjectiveHouseholderMatrixDifferentialAt k z :=
  (hasFDerivAt_coherentProjectiveHouseholderMatrix k z).fderiv

/-- Global differentiability of the packed coherent matrix chart. -/
theorem differentiable_coherentProjectiveHouseholderMatrix (k : ι) :
    Differentiable ℝ (coherentProjectiveHouseholderMatrix k) :=
  fun z => (hasFDerivAt_coherentProjectiveHouseholderMatrix k z).differentiableAt

end CoareaNative.BlockBand
