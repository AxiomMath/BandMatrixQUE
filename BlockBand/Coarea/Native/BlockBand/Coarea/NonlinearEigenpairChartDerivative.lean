module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairChartDecode
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairRealDeterminantTransport

/-!
# Joint derivative of the nonlinear eigenpair chart

The algebraic differential of the canonical eigenpair chart (energy, projective coordinate and
complementary block), and its transport to the selected chart and to the Hermitian-matrix
output of `selectedEigenpairChartDecode`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Canonical projective chart-coordinate insertion as a real-linear map. -/
def canonicalProjectiveChartCoordinatesLinearMap :
    (n → ℂ) →ₗ[ℝ]
      (ProjectiveChartCoordinate (Sum.inl Unit.unit : Unit ⊕ n) → ℂ) where
  toFun := canonicalProjectiveChartCoordinates
  map_add' z w := by
    funext j
    rcases j with ⟨j, hj⟩
    rcases j with u | j
    · exact False.elim (hj (by cases u; rfl))
    · rfl
  map_smul' c z := by
    funext j
    rcases j with ⟨j, hj⟩
    rcases j with u | j
    · exact False.elim (hj (by cases u; rfl))
    · rfl

/-- Extract the projective variable from full `(E,z,B)` coordinates. -/
def canonicalEigenpairProjectiveInputLinearMap :
    EigenpairHermitianBlockCoordinates n →ₗ[ℝ]
      (ProjectiveChartCoordinate (Sum.inl Unit.unit : Unit ⊕ n) → ℂ) :=
  canonicalProjectiveChartCoordinatesLinearMap.comp
    ((LinearMap.fst ℝ (n → ℂ) (RealHermitianMatrix n)).comp
      (LinearMap.snd ℝ ℝ ((n → ℂ) × RealHermitianMatrix n)))

/-- The block-diagonal matrix `diag(E,B)`, linearly in full chart coordinates. -/
def canonicalBlockDiagonalLinearMap :
    EigenpairHermitianBlockCoordinates n →ₗ[ℝ]
      Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ where
  toFun y := eigenpairCanonicalMatrix y.1 y.2.2.1
  map_add' y w := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [eigenpairCanonicalMatrix, eigenpairTangentColumn]
  map_smul' c y := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [eigenpairCanonicalMatrix, eigenpairTangentColumn, smul_eq_mul]

/-- Fixed two-sided matrix multiplication as a real-linear map. -/
def fixedMatrixConjugationLinearMap
    (H : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ →ₗ[ℝ]
      Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ where
  toFun A := H * A * Hᴴ
  map_add' A C := by simp [mul_add, add_mul]
  map_smul' c A := by
    change H * ((c : ℂ) • A) * Hᴴ =
      (c : ℂ) • (H * A * Hᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Algebraic joint first variation of the nonlinear decoder at `(E,0,B)`. -/
def canonicalEigenpairChartAlgebraicDifferential
    (E : ℝ) (B : RealHermitianMatrix n) :
    EigenpairHermitianBlockCoordinates n →ₗ[ℝ]
      Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  let e : Unit ⊕ n := Sum.inl Unit.unit
  let v := projectiveSelectedVector e
  let H := phaseFixedHouseholderFrame e v
  let D := eigenpairCanonicalMatrix E B.1
  (movingPhaseFixedConjugationDifferential e v D).comp
      ((projectiveChartTangentInsertion e).comp
        canonicalEigenpairProjectiveInputLinearMap) +
    (fixedMatrixConjugationLinearMap H).comp canonicalBlockDiagonalLinearMap

/-- The nonlinear canonical decoder, returned in the same block-coordinate
space as its input. -/
def canonicalEigenpairCoordinateChartDecode :
    EigenpairHermitianBlockCoordinates n →
      EigenpairHermitianBlockCoordinates n :=
  fun y => eigenpairHermitianBlockLinearEquiv n
    (canonicalEigenpairChartDecode y)

/-- The algebraic joint variation is exactly the canonical block
coordinate differential, decoded back to a Hermitian matrix.  This closes the
nonlinear matrix calculation independently of any choice of norm on the
unbundled Hermitian block-coordinate product. -/
theorem canonicalEigenpairChartAlgebraicDifferential_eq
    (E : ℝ) (B : RealHermitianMatrix n)
    (ξ : EigenpairHermitianBlockCoordinates n) :
    canonicalEigenpairChartAlgebraicDifferential E B ξ =
      ((eigenpairHermitianBlockLinearEquiv n).symm
        (eigenpairHermitianBlockCoordinateDifferential E B.1 ξ)).1 := by
  have hdH (a b : Unit ⊕ n) :
      phaseFixedHouseholderAlgebraicDifferential
          (Sum.inl Unit.unit) (projectiveSelectedVector (Sum.inl Unit.unit))
          ((projectiveChartTangentInsertion (Sum.inl Unit.unit))
            (canonicalProjectiveChartCoordinates ξ.2.1)) a b =
        (projectiveChartTangentInsertion (Sum.inl Unit.unit)
            (canonicalProjectiveChartCoordinates ξ.2.1) a) *
            (if b = Sum.inl Unit.unit then 1 else 0) +
          (if a = Sum.inl Unit.unit then 1 else 0) *
            star (projectiveChartTangentInsertion (Sum.inl Unit.unit)
              (canonicalProjectiveChartCoordinates ξ.2.1) b) := by
    exact projectiveHouseholderFrameDifferential_apply
      (Sum.inl Unit.unit) a b (canonicalProjectiveChartCoordinates ξ.2.1)
  have hins (a : n) :
      projectiveChartTangentInsertion (Sum.inl Unit.unit)
          (canonicalProjectiveChartCoordinates ξ.2.1) (Sum.inr a) =
        ξ.2.1 a := by
    rw [show Sum.inr a =
      (⟨Sum.inr a, by simp⟩ :
        ProjectiveChartCoordinate (Sum.inl Unit.unit : Unit ⊕ n)).1 by rfl]
    rw [projectiveChartTangentInsertion_apply]
    exact canonicalProjectiveChartCoordinates_inr ξ.2.1 a
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · cases a
    cases b
    simp [canonicalEigenpairChartAlgebraicDifferential,
      fixedMatrixConjugationLinearMap,
      movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential,
      canonicalEigenpairProjectiveInputLinearMap,
      canonicalProjectiveChartCoordinatesLinearMap,
      canonicalBlockDiagonalLinearMap,
      hdH, hins,
      phaseFixedHouseholderFrame_selected_apply,
      eigenpairHermitianBlockCoordinateDifferential_apply,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairGapMatrix,
      eigenpairCanonicalMatrix, eigenpairTangentColumn,
      Matrix.mul_apply]
  · cases a
    simp [canonicalEigenpairChartAlgebraicDifferential,
      fixedMatrixConjugationLinearMap,
      movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential,
      canonicalEigenpairProjectiveInputLinearMap,
      canonicalProjectiveChartCoordinatesLinearMap,
      canonicalBlockDiagonalLinearMap,
      hdH, hins,
      phaseFixedHouseholderFrame_selected_apply,
      eigenpairHermitianBlockCoordinateDifferential_apply,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairGapMatrix,
      eigenpairCanonicalMatrix, eigenpairTangentColumn,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply]
    rw [Finset.sum_eq_single b]
    · simp only [ite_eq_left, map_neg, map_one, mul_neg, mul_one]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      have hdiag :
          (∑ x, (starRingEnd ℂ) (if b = x then (E : ℂ) else 0) *
            (starRingEnd ℂ) (ξ.2.1 x)) =
            (E : ℂ) * (starRingEnd ℂ) (ξ.2.1 b) := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro c hc hcb
          simp [Ne.symm hcb]
        · simp
      rw [hdiag]
      have hB (x : n) :
          (starRingEnd ℂ) (B.1 b x) = B.1 x b := by
        exact congrFun (congrFun B.2.eq x) b
      simp_rw [hB]
      have hsum :
          (∑ x, (starRingEnd ℂ) (ξ.2.1 x) * B.1 x b) =
            ∑ x, B.1 x b * (starRingEnd ℂ) (ξ.2.1 x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      ring
    · intro c hc hcb
      simp [Ne.symm hcb]
    · simp
  · cases b
    simp [canonicalEigenpairChartAlgebraicDifferential,
      fixedMatrixConjugationLinearMap,
      movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential,
      canonicalEigenpairProjectiveInputLinearMap,
      canonicalProjectiveChartCoordinatesLinearMap,
      canonicalBlockDiagonalLinearMap,
      hdH, hins,
      phaseFixedHouseholderFrame_selected_apply,
      eigenpairHermitianBlockCoordinateDifferential_apply,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairGapMatrix,
      eigenpairCanonicalMatrix, eigenpairTangentColumn,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  · simp [canonicalEigenpairChartAlgebraicDifferential,
      fixedMatrixConjugationLinearMap,
      movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential,
      canonicalEigenpairProjectiveInputLinearMap,
      canonicalProjectiveChartCoordinatesLinearMap,
      canonicalBlockDiagonalLinearMap,
      hdH, hins,
      phaseFixedHouseholderFrame_selected_apply,
      eigenpairHermitianBlockCoordinateDifferential_apply,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairGapMatrix,
      eigenpairCanonicalMatrix, eigenpairTangentColumn,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c hc hcb
      simp [Ne.symm hcb]
    · simp

/-- Reindexing the selected-coordinate nonlinear decoder back into its own
block coordinates recovers the canonical decoder exactly. -/
theorem selectedEigenpairCoordinateChartDecode_eq_canonical
    {d : ℕ} (i : Fin d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedEigenpairCoordinateChartDecode i y =
      canonicalEigenpairCoordinateChartDecode y := by
  rw [selectedEigenpairCoordinateChartDecode, selectedEigenpairChartDecode,
    canonicalEigenpairCoordinateChartDecode]
  change eigenpairHermitianBlockLinearEquiv (Fin (d - 1))
      (selectedCoordinateHermitianReindex i
        (selectedCoordinateHermitianUnreindex i
          (canonicalEigenpairChartDecode y))) =
    eigenpairHermitianBlockLinearEquiv (Fin (d - 1))
      (canonicalEigenpairChartDecode y)
  rw [selectedCoordinateHermitian_reindex_unreindex]

/-- Algebraic joint first variation of the selected-coordinate decoder, in
the selected block coordinates.  The selected matrix coordinate only
reindexes the output and hence does not change this block-coordinate map. -/
def selectedEigenpairCoordinateChartAlgebraicDifferential
    {d : ℕ} (_i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  eigenpairHermitianBlockCoordinateDifferential E B.1

/-- In selected block coordinates the algebraic joint variation is exactly
the energy/gap/complement differential. -/
theorem selectedEigenpairCoordinateChartAlgebraicDifferential_eq
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedEigenpairCoordinateChartAlgebraicDifferential i E B ξ =
      eigenpairHermitianBlockCoordinateDifferential E B.1 ξ := by
  rfl

/-- The same joint variation transported to the Hermitian-matrix
output of `selectedEigenpairChartDecode`. -/
def selectedEigenpairChartAlgebraicDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      RealHermitianMatrix (Fin d) :=
  (selectedCoordinateEigenpairLinearEquiv i).symm.toLinearMap.comp
    (eigenpairHermitianBlockCoordinateDifferential E B.1)

/-- Transported algebraic derivative formula for the selected matrix chart. -/
theorem selectedEigenpairChartAlgebraicDifferential_apply
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedEigenpairChartAlgebraicDifferential i E B ξ =
      (selectedCoordinateEigenpairLinearEquiv i).symm
        (eigenpairHermitianBlockCoordinateDifferential E B.1 ξ) := by
  rfl

end CoareaNative.BlockBand
