module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairEntryDifferential
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairDerivativeIdentification
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairContDiff
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairLocalInverse

/-!
# Matrix packing of the coherent eigenpair differential

This module packs the scalar product-rule derivatives for the entries of
`H D Hᴴ`, then reads the packed matrix derivative back into the selected real
Hermitian coordinates.  The final equality identifies it with the paper's
canonical energy/gap/complement differential.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

private theorem matrix_productRule_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H D Hdot Ddot : ι → ι → ℂ) (a b : ι) :
    (∑ c, (
        (∑ z, H a z * D z c) * star (Hdot b c) +
        star (H b c) * (∑ z, (H a z * Ddot z c + D z c * Hdot a z)))) =
      (∑ c, (∑ z, Hdot a z * D z c) * star (H b c)) +
      (∑ c, (∑ z, H a z * D z c) * star (Hdot b c)) +
      (∑ c, (∑ z, H a z * Ddot z c) * star (H b c)) := by
  simp [Finset.sum_add_distrib, mul_add]
  have hswap :
      (∑ x, (starRingEnd ℂ) (H b x) * ∑ x₁, D x₁ x * Hdot a x₁) =
        ∑ x, (∑ x₁, Hdot a x₁ * D x₁ x) * (starRingEnd ℂ) (H b x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x₁ _
    ring
  have hswap' :
      (∑ x, (starRingEnd ℂ) (H b x) * ∑ x₁, H a x₁ * Ddot x₁ x) =
        ∑ x, (∑ x₁, H a x₁ * Ddot x₁ x) * (starRingEnd ℂ) (H b x) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hswap, hswap']
  abel

/-- The explicit entrywise derivative, packed into a matrix-valued continuous
linear map. -/
def coherentEigenpairMatrixDifferential {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →L[ℝ]
      Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  ContinuousLinearMap.pi fun a =>
    ContinuousLinearMap.pi fun b =>
      coherentEigenpairConjugationEntryDifferential i E B a b

/-- The explicit entrywise derivative, flattened into the Euclidean matrix
coordinate carrier. -/
def coherentEigenpairEuclideanDifferential {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →L[ℝ]
      EuclideanSpace ℂ
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) :=
  ((LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) ℂ).symm.toLinearEquiv.restrictScalars ℝ)) :
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) ≃L[ℝ]
        EuclideanSpace ℂ
          ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1)))).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ab =>
      coherentEigenpairConjugationEntryDifferential i E B ab.1 ab.2)

/-- The explicit Euclidean derivative packed into the coherent matrix carrier. -/
def coherentEigenpairPackedMatrixDifferential {d : ℕ}
    (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →L[ℝ]
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) :=
  (coherentCarrierWrapCLM
    (EuclideanSpace ℂ
      ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))))).comp
    (coherentEigenpairEuclideanDifferential i E B)

/-- The Euclidean matrix formula has the packed coordinatewise derivative. -/
theorem hasFDerivAt_coherentEigenpairConjugationEuclidean_explicit_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentEigenpairConjugationEuclidean i)
      (coherentEigenpairEuclideanDifferential i E B)
      (coherentEigenpairZeroInput i E B) := by
  have hfun : HasFDerivAt
      (fun x : CoherentHermitianCoordinates d =>
        fun ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1)) =>
          coherentEigenpairConjugationEntry i ab.1 ab.2 x)
      (ContinuousLinearMap.pi fun ab =>
        coherentEigenpairConjugationEntryDifferential i E B ab.1 ab.2)
      (coherentEigenpairZeroInput i E B) := by
    rw [hasFDerivAt_pi]
    intro ab
    exact hasFDerivAt_coherentEigenpairConjugationEntry_zero
      i E B ab.1 ab.2
  let eR : EuclideanSpace ℂ
      ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) ≃L[ℝ]
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv _ ℂ).toLinearEquiv.restrictScalars ℝ)
  have h := eR.symm.hasFDerivAt.comp
    (coherentEigenpairZeroInput i E B) hfun
  convert h using 1
  · funext x
    rfl
  · rfl

/-- The coherent joint reconstruction has the explicit packed matrix
product-rule derivative. -/
theorem hasFDerivAt_coherentEigenpairConjugation_explicit_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentEigenpairConjugation i)
      (coherentEigenpairPackedMatrixDifferential i E B)
      (coherentEigenpairZeroInput i E B) := by
  have h := (coherentCarrierWrapCLM
      (EuclideanSpace ℂ
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))))).hasFDerivAt.comp
    (coherentEigenpairZeroInput i E B)
    (hasFDerivAt_coherentEigenpairConjugationEuclidean_explicit_zero i E B)
  convert h using 1
  · funext x
    rfl
  · rfl

/-- Selected-coordinate readback of the explicit packed matrix derivative. -/
def coherentEigenpairReadbackMatrixDifferential {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedMatrixReadbackCLM i).comp
    (coherentEigenpairPackedMatrixDifferential i E B)

/-- The selected-coordinate decoder has the explicit readback derivative. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode_explicit_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (coherentEigenpairReadbackMatrixDifferential i E B)
      (coherentEigenpairZeroInput i E B) := by
  exact (coherentSelectedMatrixReadbackCLM i).hasFDerivAt.comp _
    (hasFDerivAt_coherentEigenpairConjugation_explicit_zero i E B)

/-- After selected-coordinate readback, the explicit product-rule derivative
is the coherent lift of the canonical energy/gap/complement differential. -/
theorem coherentEigenpairReadbackMatrixDifferential_eq {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    coherentEigenpairReadbackMatrixDifferential i E B =
      coherentLiftCLM
        (selectedEigenpairFinCoordinateDifferential i E B).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply congrArg CoherentAnalyticCarrier.mk
  -- The remaining equality is precisely the algebraic chart differential.
  change selectedMatrixFinCoordinateReadCLM i
      (fun a b => coherentEigenpairConjugationEntryDifferential i E B a b u) =
    selectedEigenpairFinCoordinateDifferential i E B u.value
  rw [selectedEigenpairFinCoordinateDifferential_apply]
  let ξ := selectedEigenpairFinCoordinateLinearEquiv i u.value
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let x0 := coherentEigenpairZeroInput i E B
  have hP0 :
      coherentSelectedProjectiveInputCLM i x0 =
        (⟨0⟩ : CoherentProjectiveCoordinates e) :=
    coherentSelectedProjectiveInput_zeroInput i E B
  have hx0 :
      coherentSelectedBlockInputLinearMap i x0 =
        (E, ((0 : Fin (d - 1) → ℂ), B)) := by
    change (selectedEigenpairFinCoordinateLinearEquiv i)
      (selectedEigenpairZeroSliceCoordinates i E B) = _
    rw [selectedEigenpairZeroSliceCoordinates,
      (selectedEigenpairFinCoordinateLinearEquiv i).apply_symm_apply]
  have hH0 (p q : Unit ⊕ Fin (d - 1)) :
      coherentProjectiveHouseholderFrame e
          (coherentSelectedProjectiveInputCLM i x0) p q =
        phaseFixedHouseholderFrame e (projectiveSelectedVector e) p q := by
    rw [hP0]
    change phaseFixedHouseholderFrame e
      (projectiveUnitReconstruction e 0) p q = _
    rw [projectiveUnitReconstruction_zero]
  have hD0 (p q : Unit ⊕ Fin (d - 1)) :
      coherentBlockDiagonalEntryCLM i p q x0 =
        eigenpairCanonicalMatrix E B.1 p q := by
    simp [coherentBlockDiagonalEntryCLM, hx0,
      canonicalBlockDiagonalLinearMap, eigenpairCanonicalMatrix,
      matrixEntryEvaluationCLM]
  have hv0 :
      (coherentEigenpairZeroUnit i E B).value =
        projectiveSelectedVector e := by
    rw [coherentEigenpairZeroUnit, hP0]
    change projectiveUnitReconstruction e 0 = _
    rw [projectiveUnitReconstruction_zero]
  have htangent :
      (((coherentProjectiveChartTangentInsertion e).comp
        (coherentSelectedProjectiveInputCLM i)) u).value =
        projectiveChartTangentInsertion e
          (canonicalEigenpairProjectiveInputLinearMap ξ) := by
    rfl
  have hH' (p q : Unit ⊕ Fin (d - 1)) :
      coherentEigenpairHouseholderEntryDifferential i E B p q u =
        phaseFixedHouseholderAlgebraicDifferential e
          (projectiveSelectedVector e)
          (projectiveChartTangentInsertion e
            (canonicalEigenpairProjectiveInputLinearMap ξ)) p q := by
    change phaseFixedHouseholderAlgebraicDifferential e
      (coherentEigenpairZeroUnit i E B).value
      (((coherentProjectiveChartTangentInsertion e).comp
        (coherentSelectedProjectiveInputCLM i)) u).value p q = _
    rw [hv0, htangent]
  have hD' (p q : Unit ⊕ Fin (d - 1)) :
      coherentEigenpairBlockEntryDifferential i E B p q u =
        canonicalBlockDiagonalLinearMap ξ p q := by
    simp [coherentEigenpairBlockEntryDifferential,
      coherentBlockDiagonalEntryCLM, ξ,
      coherentSelectedBlockInputLinearMap, matrixEntryEvaluationCLM]
    rfl
  have hH0mat :
      coherentProjectiveHouseholderFrame e
          (coherentSelectedProjectiveInputCLM i x0) =
        phaseFixedHouseholderFrame e (projectiveSelectedVector e) := by
    ext p q
    exact hH0 p q
  have hD0fun :
      (fun p q => coherentBlockDiagonalEntryCLM i p q x0) =
        eigenpairCanonicalMatrix E B.1 := by
    funext p q
    exact hD0 p q
  have hH'fun :
      (fun p q => coherentEigenpairHouseholderEntryDifferential i E B p q u) =
        phaseFixedHouseholderAlgebraicDifferential e
          (projectiveSelectedVector e)
          (projectiveChartTangentInsertion e
            (canonicalEigenpairProjectiveInputLinearMap ξ)) := by
    funext p q
    exact hH' p q
  have hD'fun :
      (fun p q => coherentEigenpairBlockEntryDifferential i E B p q u) =
        canonicalBlockDiagonalLinearMap ξ := by
    funext p q
    exact hD' p q
  let productRuleEntry :=
    fun (H D Hdot Ddot :
        (Unit ⊕ Fin (d - 1)) → (Unit ⊕ Fin (d - 1)) → ℂ)
      (a b : Unit ⊕ Fin (d - 1)) =>
      ∑ c, (
        (∑ z, H a z * D z c) * star (Hdot b c) +
        star (H b c) * (∑ z, (H a z * Ddot z c + D z c * Hdot a z)))
  let expandedProductRuleEntry :=
    fun (H D Hdot Ddot :
        (Unit ⊕ Fin (d - 1)) → (Unit ⊕ Fin (d - 1)) → ℂ)
      (a b : Unit ⊕ Fin (d - 1)) =>
      (∑ c, (∑ z, Hdot a z * D z c) * star (H b c)) +
      (∑ c, (∑ z, H a z * D z c) * star (Hdot b c)) +
      (∑ c, (∑ z, H a z * Ddot z c) * star (H b c))
  have hmatrix :
      (fun a b => coherentEigenpairConjugationEntryDifferential i E B a b u) =
        canonicalEigenpairChartAlgebraicDifferential E B ξ := by
    ext a b
    simp only [coherentEigenpairConjugationEntryDifferential,
      _root_.sum_apply, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    change productRuleEntry
      (coherentProjectiveHouseholderFrame e
        (coherentSelectedProjectiveInputCLM i x0))
      (fun p q => coherentBlockDiagonalEntryCLM i p q x0)
      (fun p q => coherentEigenpairHouseholderEntryDifferential i E B p q u)
      (fun p q => coherentEigenpairBlockEntryDifferential i E B p q u) a b =
        canonicalEigenpairChartAlgebraicDifferential E B ξ a b
    calc
      _ = expandedProductRuleEntry
          (coherentProjectiveHouseholderFrame e
            (coherentSelectedProjectiveInputCLM i x0))
          (fun p q => coherentBlockDiagonalEntryCLM i p q x0)
          (fun p q =>
            coherentEigenpairHouseholderEntryDifferential i E B p q u)
          (fun p q =>
            coherentEigenpairBlockEntryDifferential i E B p q u) a b := by
            dsimp only [productRuleEntry, expandedProductRuleEntry]
            exact matrix_productRule_entry
              (ι := Unit ⊕ Fin (d - 1))
              (coherentProjectiveHouseholderFrame e
                (coherentSelectedProjectiveInputCLM i x0))
              (fun p q => coherentBlockDiagonalEntryCLM i p q x0)
              (fun p q =>
                coherentEigenpairHouseholderEntryDifferential i E B p q u)
              (fun p q =>
                coherentEigenpairBlockEntryDifferential i E B p q u) a b
      _ = canonicalEigenpairChartAlgebraicDifferential E B ξ a b := by
        dsimp only [expandedProductRuleEntry]
        simp_rw [hH0, hD0, hH', hD']
        change _ =
          (movingUnitaryConjugationAlgebraicDifferential
              (phaseFixedHouseholderFrame e (projectiveSelectedVector e))
              (phaseFixedHouseholderAlgebraicDifferential e
                (projectiveSelectedVector e)
                (projectiveChartTangentInsertion e
                  (canonicalEigenpairProjectiveInputLinearMap ξ)))
              (eigenpairCanonicalMatrix E B.1) +
            phaseFixedHouseholderFrame e (projectiveSelectedVector e) *
              canonicalBlockDiagonalLinearMap ξ *
              (phaseFixedHouseholderFrame e
                (projectiveSelectedVector e))ᴴ) a b
        simp only [movingUnitaryConjugationAlgebraicDifferential,
          Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hmatrix, canonicalEigenpairChartAlgebraicDifferential_eq]
  exact selectedMatrixFinCoordinateRead_decode i
    (eigenpairHermitianBlockCoordinateDifferential E B.1 ξ)

/-- The derivative previously defined through `fderiv` is the explicit packed
entrywise derivative. -/
theorem coherentSelectedEigenpairReadbackDifferential_eq_explicit {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    coherentSelectedEigenpairReadbackDifferential i E B =
      coherentEigenpairReadbackMatrixDifferential i E B := by
  exact (hasFDerivAt_coherentSelectedEigenpairDecode_zero i E B).unique
    (hasFDerivAt_coherentSelectedEigenpairDecode_explicit_zero i E B)

/-- The coherent derivative is the canonical gap differential
transported through the selected coordinate equivalence. -/
theorem coherentSelectedEigenpairDerivativeIdentified_of_gap {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    CoherentSelectedEigenpairDerivativeIdentified i E B hgap := by
  rw [CoherentSelectedEigenpairDerivativeIdentified,
    coherentSelectedEigenpairReadbackDifferential_eq_explicit,
    coherentEigenpairReadbackMatrixDifferential_eq]
  apply ContinuousLinearMap.ext
  intro u
  apply congrArg CoherentAnalyticCarrier.mk
  rfl

/-- The selected coherent eigenpair decoder is locally a homeomorphism at
every zero-slice point whose energy is outside the complementary spectrum. -/
def coherentSelectedEigenpairLocalHomeomorphOfGap {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    OpenPartialHomeomorph (CoherentHermitianCoordinates d)
      (CoherentHermitianCoordinates d) :=
  coherentSelectedEigenpairLocalHomeomorph i E B hgap
    ((contDiffAt_coherentSelectedEigenpairDecode i
      (coherentSelectedEigenpairZeroInput i E B)).of_le (by norm_num))
    (coherentSelectedEigenpairDerivativeIdentified_of_gap i E B hgap)

@[simp] theorem coherentSelectedEigenpairLocalHomeomorphOfGap_coe {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    (coherentSelectedEigenpairLocalHomeomorphOfGap i E B hgap :
      CoherentHermitianCoordinates d → CoherentHermitianCoordinates d) =
        coherentSelectedEigenpairDecode i := by
  rfl

/-- The zero-slice base point lies in the source of the unconditional local
homeomorphism. -/
theorem coherentSelectedEigenpairZeroInput_mem_localHomeomorphOfGap_source
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    coherentSelectedEigenpairZeroInput i E B ∈
      (coherentSelectedEigenpairLocalHomeomorphOfGap i E B hgap).source := by
  exact coherentSelectedEigenpairZeroInput_mem_localHomeomorph_source
    i E B hgap
    ((contDiffAt_coherentSelectedEigenpairDecode i
      (coherentSelectedEigenpairZeroInput i E B)).of_le (by norm_num))
    (coherentSelectedEigenpairDerivativeIdentified_of_gap i E B hgap)

end CoareaNative.BlockBand
