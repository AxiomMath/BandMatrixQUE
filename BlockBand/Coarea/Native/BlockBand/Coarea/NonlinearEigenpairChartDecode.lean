module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveHouseholderFrameDerivative
public import BlockBand.Coarea.Native.BlockBand.Coarea.MovingHouseholderConjugationDerivative

/-!
# Nonlinear phase-fixed eigenpair chart decoding

This module constructs the same-dimensional nonlinear chart map in
energy, projective, and complementary-Hermitian coordinates.  The canonical
chart first normalizes the affine projective coordinate, completes it by the
explicit Householder frame, and conjugates the block diagonal matrix
`diag(E,B)`.  Reindexing transports the construction to any selected matrix
coordinate.

The construction is unconditional and exact.  We prove that the reconstructed
phase-fixed vector is a unit eigenvector with eigenvalue `E`, and that the chart
fixes the entire zero-projective-coordinate slice.  The joint Fréchet derivative
of this `(E,z,B)` map is treated separately
(`hasFDerivAt_phaseFixedHouseholder_joint_conjugation`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Complementary affine coordinates in the canonical `Unit ⊕ n` chart. -/
def canonicalProjectiveChartCoordinates (z : n → ℂ)
    (j : ProjectiveChartCoordinate (Sum.inl Unit.unit : Unit ⊕ n)) : ℂ := by
  rcases j with ⟨u | a, h⟩
  · exact False.elim (h (by cases u; rfl))
  · exact z a

@[simp] theorem canonicalProjectiveChartCoordinates_inr
    (z : n → ℂ) (j : n) :
    canonicalProjectiveChartCoordinates z
      ⟨Sum.inr j, by simp⟩ = z j := by
  rfl

@[simp] theorem canonicalProjectiveChartCoordinates_zero :
    canonicalProjectiveChartCoordinates (0 : n → ℂ) = 0 := by
  funext j
  rcases j with ⟨j, hj⟩
  rcases j with u | j
  · exact False.elim (hj (by cases u; rfl))
  · rfl

/-- The canonical phase-fixed unit eigenvector associated with affine
projective coordinate `z`. -/
def canonicalProjectiveUnitVector (z : n → ℂ) :
    EuclideanSpace ℂ (Unit ⊕ n) :=
  projectiveUnitReconstruction (Sum.inl Unit.unit)
    (canonicalProjectiveChartCoordinates z)

@[simp] theorem norm_canonicalProjectiveUnitVector (z : n → ℂ) :
    ‖canonicalProjectiveUnitVector z‖ = 1 :=
  norm_projectiveUnitReconstruction _ _

@[simp] theorem canonicalProjectiveUnitVector_selected (z : n → ℂ) :
    canonicalProjectiveUnitVector z (Sum.inl Unit.unit) =
      ((‖projectiveEigenvectorReconstruction (Sum.inl Unit.unit)
        (canonicalProjectiveChartCoordinates z)‖⁻¹ : ℝ) : ℂ) :=
  projectiveUnitReconstruction_apply_self _ _

/-- The selected coordinate of the canonical unit vector is positive real. -/
theorem canonicalProjectiveUnitVector_selected_re_pos (z : n → ℂ) :
    0 < (canonicalProjectiveUnitVector z (Sum.inl Unit.unit)).re :=
  projectiveUnitReconstruction_self_re_pos _ _

/-- The canonical nonlinear eigenpair decoder in block coordinates. -/
def canonicalEigenpairChartDecode
    (y : EigenpairHermitianBlockCoordinates n) :
    RealHermitianMatrix (Unit ⊕ n) :=
  let v := canonicalProjectiveUnitVector y.2.1
  let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit) v
  let D := (eigenpairHermitianBlockLinearEquiv n).symm
    (y.1, ((0 : n → ℂ), y.2.2))
  ⟨H * D.1 * Hᴴ, by
    change (H * D.1 * Hᴴ).IsHermitian
    simpa only [Matrix.conjTranspose_conjTranspose] using
      isHermitian_unitaryConjugation Hᴴ D.1 D.2⟩

/-- The Householder frame sends the selected coordinate vector to the
phase-fixed projective representative. -/
theorem phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector
    (z : n → ℂ) :
    (phaseFixedHouseholderFrame (Sum.inl Unit.unit)
      (canonicalProjectiveUnitVector z)).mulVec
        (phaseFixedCoordinateVector (Sum.inl Unit.unit)) =
      canonicalProjectiveUnitVector z := by
  apply phaseFixedHouseholderFrame_mulVec_coordinate
  · apply Complex.ext
    · rfl
    · simp [canonicalProjectiveUnitVector,
        projectiveUnitReconstruction_apply_self]
  · exact ne_of_gt (phaseFixedHouseholder_denominator_pos _ _
      (canonicalProjectiveUnitVector_selected_re_pos z))

/-- The canonical block matrix acts on the distinguished coordinate vector by
its selected energy. -/
theorem eigenpairCanonicalMatrix_mulVec_coordinate
    (E : ℝ) (B : Matrix n n ℂ) :
    (eigenpairCanonicalMatrix E B).mulVec
      (phaseFixedCoordinateVector (Sum.inl Unit.unit)) =
        (E : ℂ) • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
  funext i
  rcases i with u | i
  · cases u
    simp [eigenpairCanonicalMatrix, phaseFixedCoordinateVector,
      Matrix.mulVec, eigenpairTangentColumn]
  · simp [eigenpairCanonicalMatrix, phaseFixedCoordinateVector,
      Matrix.mulVec, eigenpairTangentColumn]

/-- The decoded phase-fixed vector is an eigenvector of the decoded
Hermitian matrix with eigenvalue `E`. -/
theorem canonicalEigenpairChartDecode_mulVec_unitVector
    (y : EigenpairHermitianBlockCoordinates n) :
    (canonicalEigenpairChartDecode y).1.mulVec
      (canonicalProjectiveUnitVector y.2.1) =
        (y.1 : ℂ) • canonicalProjectiveUnitVector y.2.1 := by
  let v := canonicalProjectiveUnitVector y.2.1
  let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit) v
  let e : (Unit ⊕ n) → ℂ :=
    phaseFixedCoordinateVector (Sum.inl Unit.unit)
  have hv : H.mulVec e = v :=
    phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector y.2.1
  have hunit : Hᴴ * H =
      (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) := by
    apply phaseFixedHouseholderFrame_unitary
    · exact norm_canonicalProjectiveUnitVector _
    · apply Complex.ext
      · rfl
      · rw [canonicalProjectiveUnitVector_selected]
        simp
    · exact canonicalProjectiveUnitVector_selected_re_pos _
  change ((H * ((eigenpairHermitianBlockLinearEquiv n).symm
    (y.1, ((0 : n → ℂ), y.2.2))).1 * Hᴴ).mulVec v) = _
  have hD : ((eigenpairHermitianBlockLinearEquiv n).symm
      (y.1, ((0 : n → ℂ), y.2.2))).1 =
      eigenpairCanonicalMatrix y.1 y.2.2.1 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [eigenpairHermitianBlockLinearEquiv_symm_apply,
        decodeEigenpairHermitianBlocks, eigenpairCanonicalMatrix,
        eigenpairTangentColumn]
  rw [hD]
  rw [← hv]
  calc
    (H * eigenpairCanonicalMatrix y.1 y.2.2.1 * Hᴴ).mulVec (H.mulVec e) =
        ((H * eigenpairCanonicalMatrix y.1 y.2.2.1 * Hᴴ) * H).mulVec e := by
          rw [Matrix.mulVec_mulVec]
    _ = (H * eigenpairCanonicalMatrix y.1 y.2.2.1 * (Hᴴ * H)).mulVec e := by
          congr 1
          noncomm_ring
    _ = (H * eigenpairCanonicalMatrix y.1 y.2.2.1).mulVec e := by rw [hunit]; simp
    _ = H.mulVec ((eigenpairCanonicalMatrix y.1 y.2.2.1).mulVec e) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = H.mulVec ((y.1 : ℂ) • e) := by rw [eigenpairCanonicalMatrix_mulVec_coordinate]
    _ = (y.1 : ℂ) • H.mulVec e := Matrix.mulVec_smul _ _ _

/-- At zero projective coordinate the unit vector is the distinguished
coordinate vector. -/
@[simp] theorem canonicalProjectiveUnitVector_zero :
    canonicalProjectiveUnitVector (0 : n → ℂ) =
      projectiveSelectedVector (Sum.inl Unit.unit : Unit ⊕ n) := by
  simp [canonicalProjectiveUnitVector]

/-- At the selected basis vector the phase-fixed Householder frame is the
signature matrix which is `+1` on the selected coordinate and `-1` on its
complement. -/
theorem phaseFixedHouseholderFrame_selected_apply
    (a b : Unit ⊕ n) :
    phaseFixedHouseholderFrame (Sum.inl Unit.unit)
      (projectiveSelectedVector (Sum.inl Unit.unit : Unit ⊕ n)) a b =
      if a = b then (if a = Sum.inl Unit.unit then 1 else -1) else 0 := by
  rw [phaseFixedHouseholderFrame_apply]
  by_cases hab : a = b
  · subst b
    by_cases ha : a = Sum.inl Unit.unit
    · subst a
      norm_num [phaseFixedHouseholderShift, projectiveSelectedVector,
        projectiveEigenvectorReconstruction, phaseFixedCoordinateVector]
    · simp [phaseFixedHouseholderShift, projectiveSelectedVector,
        projectiveEigenvectorReconstruction, phaseFixedCoordinateVector, ha]
  · by_cases ha : a = Sum.inl Unit.unit
    · have hb : b ≠ Sum.inl Unit.unit := by
        intro hb
        exact hab (ha.trans hb.symm)
      have hb' : Sum.inl Unit.unit ≠ b := Ne.symm hb
      simp [phaseFixedHouseholderShift, projectiveSelectedVector,
        projectiveEigenvectorReconstruction, phaseFixedCoordinateVector,
        hab, ha, hb, hb']
    · by_cases hb : b = Sum.inl Unit.unit
      · have ha' : Sum.inl Unit.unit ≠ a := Ne.symm ha
        simp [phaseFixedHouseholderShift, projectiveSelectedVector,
          projectiveEigenvectorReconstruction, phaseFixedCoordinateVector,
          hab, ha, ha', hb]
      · have ha' : Sum.inl Unit.unit ≠ a := Ne.symm ha
        have hb' : Sum.inl Unit.unit ≠ b := Ne.symm hb
        simp [phaseFixedHouseholderShift, projectiveSelectedVector,
          projectiveEigenvectorReconstruction, phaseFixedCoordinateVector,
          hab, ha, ha', hb, hb']

/-- The canonical nonlinear decoder fixes the entire zero-projective slice. -/
@[simp] theorem canonicalEigenpairChartDecode_zero_tangent
    (E : ℝ) (B : RealHermitianMatrix n) :
    canonicalEigenpairChartDecode (E, ((0 : n → ℂ), B)) =
      (eigenpairHermitianBlockLinearEquiv n).symm
        (E, ((0 : n → ℂ), B)) := by
  apply Subtype.ext
  ext a b
  rcases a with u | a <;> rcases b with v | b
  · cases u
    cases v
    simp [canonicalEigenpairChartDecode, eigenpairCanonicalMatrix,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks,
      phaseFixedHouseholderFrame_selected_apply, Matrix.mul_apply,
      eigenpairTangentColumn]
  · cases u
    simp [canonicalEigenpairChartDecode, eigenpairCanonicalMatrix,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks,
      phaseFixedHouseholderFrame_selected_apply, Matrix.mul_apply,
      eigenpairTangentColumn]
  · cases v
    simp [canonicalEigenpairChartDecode, eigenpairCanonicalMatrix,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks,
      phaseFixedHouseholderFrame_selected_apply, Matrix.mul_apply,
      eigenpairTangentColumn]
  · simp [canonicalEigenpairChartDecode, eigenpairCanonicalMatrix,
      eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks,
      phaseFixedHouseholderFrame_selected_apply, Matrix.mul_apply,
      eigenpairTangentColumn]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c hc hcb
      simp [Ne.symm hcb]
    · simp

/-- Transport the canonical nonlinear decoder to an arbitrary selected matrix
coordinate. -/
def selectedEigenpairChartDecode {d : ℕ} (i : Fin d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    RealHermitianMatrix (Fin d) :=
  selectedCoordinateHermitianUnreindex i
    (canonicalEigenpairChartDecode y)

/-- In selected block coordinates, the nonlinear decoder is a
same-dimensional self-map. -/
def selectedEigenpairCoordinateChartDecode {d : ℕ} (i : Fin d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  fun y => selectedCoordinateEigenpairLinearEquiv i
    (selectedEigenpairChartDecode i y)

/-- The arbitrary-selected-coordinate decoder also fixes its full
zero-projective slice. -/
@[simp] theorem selectedEigenpairCoordinateChartDecode_zero_tangent
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    selectedEigenpairCoordinateChartDecode i
      (E, ((0 : Fin (d - 1) → ℂ), B)) =
        (E, ((0 : Fin (d - 1) → ℂ), B)) := by
  rw [selectedEigenpairCoordinateChartDecode, selectedEigenpairChartDecode,
    canonicalEigenpairChartDecode_zero_tangent]
  exact (selectedCoordinateEigenpairLinearEquiv i).apply_symm_apply _

end CoareaNative.BlockBand
