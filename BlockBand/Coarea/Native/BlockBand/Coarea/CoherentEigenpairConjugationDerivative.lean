module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairJointDerivative

/-!
# Coherent joint eigenpair conjugation derivative

The conjugation `t ↦ U(t) D U(t)ᴴ` of a block-diagonal matrix `D = diag(E, B)` by the coherent
eigenpair frame is differentiable at `t = 0`, with an explicit Fréchet derivative in Euclidean
coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- A scalar entry of the coherent canonical block-diagonal input. -/
def coherentBlockDiagonalEntryCLM {d : ℕ} (i : Fin d)
    (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  (matrixEntryEvaluationCLM a b).comp
    (matrixLinearMapToContinuous
      (canonicalBlockDiagonalLinearMap.comp
        (coherentSelectedBlockInputLinearMap i)))

/-- The coherent joint reconstruction, packed into Euclidean matrix entries. -/
def coherentEigenpairConjugationEuclidean {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d →
      EuclideanSpace ℂ ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) :=
  fun x =>
    let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
    let z := coherentSelectedProjectiveInputCLM i x
    let H := coherentProjectiveHouseholderFrame e z
    let D := canonicalBlockDiagonalLinearMap
      (coherentSelectedBlockInputLinearMap i x)
    WithLp.toLp 2 fun ab => (H * D * Matrix.conjTranspose H) ab.1 ab.2

/-- Joint reconstruction with coherent matrix output. -/
def coherentEigenpairConjugation {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d →
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) :=
  fun x => ⟨coherentEigenpairConjugationEuclidean i x⟩

/-- The full finite product-rule calculation proves differentiability
of coherent joint conjugation at every selected zero-projective slice. -/
theorem differentiableAt_coherentEigenpairConjugation_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    DifferentiableAt ℝ (coherentEigenpairConjugation i)
      (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
        CoherentHermitianCoordinates d) := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let x0 : CoherentHermitianCoordinates d :=
    ⟨selectedEigenpairZeroSliceCoordinates i E B⟩
  let P := coherentSelectedProjectiveInputCLM i
  have hP0 : P x0 = (⟨0⟩ : CoherentProjectiveCoordinates e) :=
    coherentSelectedProjectiveInputCLM_zeroSlice i E B
  have hunit : DifferentiableAt ℝ
      (fun x => coherentProjectiveUnitReconstruction e (P x)) x0 := by
    have h := hasFDerivAt_coherentProjectiveUnitReconstruction_zero e
    rw [← hP0] at h
    exact (h.comp x0 P.hasFDerivAt).differentiableAt
  have hH (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x => coherentProjectiveHouseholderFrame e (P x) a b) x0 := by
    change DifferentiableAt ℝ (fun x =>
      coherentPhaseFixedHouseholderFrameEntry e a b
        (coherentProjectiveUnitReconstruction e (P x))) x0
    have hv : 1 + ((coherentProjectiveUnitReconstruction e (P x0)).value e).re ≠ 0 := by
      rw [hP0]
      simp [coherentProjectiveUnitReconstruction, coherentLift,
        projectiveSelectedVector, projectiveEigenvectorReconstruction]
    exact (differentiableAt_coherentPhaseFixedHouseholderFrameEntry e a b _ hv).comp
      x0 hunit
  have hD (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x => coherentBlockDiagonalEntryCLM i a b x) x0 :=
    (coherentBlockDiagonalEntryCLM i a b).differentiableAt
  have hentry (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x =>
        let H := coherentProjectiveHouseholderFrame e (P x)
        let D := canonicalBlockDiagonalLinearMap
          (coherentSelectedBlockInputLinearMap i x)
        (H * D * Matrix.conjTranspose H) a b) x0 := by
    change DifferentiableAt ℝ (fun x => ∑ c, (∑ z,
      coherentProjectiveHouseholderFrame e (P x) a z *
        coherentBlockDiagonalEntryCLM i z c x) *
      star (coherentProjectiveHouseholderFrame e (P x) b c)) x0
    fun_prop
  have hfun : DifferentiableAt ℝ (fun x => fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) =>
      let H := coherentProjectiveHouseholderFrame e (P x)
      let D := canonicalBlockDiagonalLinearMap
        (coherentSelectedBlockInputLinearMap i x)
      (H * D * Matrix.conjTranspose H) ab.1 ab.2) x0 :=
    differentiableAt_pi.mpr fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) => hentry ab.1 ab.2
  let eR : EuclideanSpace ℂ ((Unit ⊕ Fin (d - 1)) ×
      (Unit ⊕ Fin (d - 1))) ≃L[ℝ]
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv _ ℂ).toLinearEquiv.restrictScalars ℝ)
  have heuclid : DifferentiableAt ℝ
      (coherentEigenpairConjugationEuclidean i) x0 := by
    have h := eR.symm.differentiableAt.comp x0 hfun
    convert h using 1
    funext x
    rfl
  change DifferentiableAt ℝ (fun x =>
    (⟨coherentEigenpairConjugationEuclidean i x⟩ :
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)))) x0
  exact (HasFDerivAt.coherentOutput heuclid.hasFDerivAt).differentiableAt

/-- Fréchet derivative, with its exact uniquely determined term. -/
theorem hasFDerivAt_coherentEigenpairConjugation_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentEigenpairConjugation i)
      (fderiv ℝ (coherentEigenpairConjugation i)
        (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
          CoherentHermitianCoordinates d))
      (⟨selectedEigenpairZeroSliceCoordinates i E B⟩ :
        CoherentHermitianCoordinates d) :=
  (differentiableAt_coherentEigenpairConjugation_zero i E B).hasFDerivAt

end CoareaNative.BlockBand
