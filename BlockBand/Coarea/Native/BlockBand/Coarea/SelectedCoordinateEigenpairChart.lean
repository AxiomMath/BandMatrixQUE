module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HouseholderEigenpairCoordinates
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Selected-coordinate Hermitian eigenpair charts

This module transports the canonical `Unit ⊕ Fin (d-1)` eigenpair block split
to an arbitrary distinguished coordinate of `Fin d`.  The distinguished index
is sent to the `Unit` summand and `Fin.succAbove` supplies the complementary
indices.  Reindexing preserves Hermitian matrices and gives a real-linear
equivalence with the energy/tangent/complement coordinate space.

This handles the discrete reindexing and dimension bookkeeping needed by the
phase-fixed Householder construction.  An `OrderedEigenpairSmoothChartCompletion`
also needs the full real derivative of the coordinate-dependent Householder
conjugation in affine projective coordinates, which is not part of this module;
the fixed-frame derivative and its canonical gap block are proved separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The elementary equivalence `Option α ≃ Unit ⊕ α`, with `none` as the
selected coordinate. -/
def optionEquivUnitSum (α : Type*) : Option α ≃ Unit ⊕ α where
  toFun
    | none => Sum.inl Unit.unit
    | some a => Sum.inr a
  invFun
    | Sum.inl _ => none
    | Sum.inr a => some a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (_ | a) <;> rfl

/-- Reindex `Fin d` by putting an arbitrary selected coordinate first.
The existence of `i : Fin d` supplies the required positivity of `d`. -/
def selectedCoordinateEquiv {d : ℕ} (i : Fin d) :
    Fin d ≃ Unit ⊕ Fin (d - 1) := by
  have hi : i.val < d := i.isLt
  have hd : d = (d - 1) + 1 := by omega
  let e : Fin d ≃ Fin ((d - 1) + 1) := finCongr hd
  exact e |>.trans (finSuccEquiv' (e i)) |>.trans
    (optionEquivUnitSum (Fin (d - 1)))

/-- The selected index is exactly the `Unit` coordinate. -/
theorem selectedCoordinateEquiv_apply_selected
    {d : ℕ} (i : Fin d) :
    selectedCoordinateEquiv i i = Sum.inl Unit.unit := by
  apply (selectedCoordinateEquiv i).symm.injective
  simp [selectedCoordinateEquiv, optionEquivUnitSum,
    finSuccEquiv'_symm_none]

/-- Every complementary coordinate is obtained by the inverse selected-index
reindexing. -/
theorem selectedCoordinateEquiv_symm_ne_selected
    {d : ℕ} (i : Fin d) (j : Fin (d - 1)) :
    (selectedCoordinateEquiv i).symm (Sum.inr j) ≠ i := by
  intro h
  have := congrArg (selectedCoordinateEquiv i) h
  simp [selectedCoordinateEquiv_apply_selected] at this

/-- Matrix reindexing along an equivalence preserves Hermitianity. -/
theorem isHermitian_reindex_equiv
    {m n : Type*} (e : m ≃ n) (A : Matrix m m ℂ)
    (hA : A.IsHermitian) :
    (Matrix.reindex e e A).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  exact hA.apply (e.symm i) (e.symm j)

/-- Hermitian reindexing to the selected-coordinate decomposition. -/
def selectedCoordinateHermitianReindex
    {d : ℕ} (i : Fin d) :
    RealHermitianMatrix (Fin d) →
      RealHermitianMatrix (Unit ⊕ Fin (d - 1)) :=
  fun A =>
    ⟨Matrix.reindex (selectedCoordinateEquiv i)
      (selectedCoordinateEquiv i) A.1,
      isHermitian_reindex_equiv (selectedCoordinateEquiv i) A.1 A.2⟩

/-- Inverse Hermitian reindexing from the selected-coordinate decomposition. -/
def selectedCoordinateHermitianUnreindex
    {d : ℕ} (i : Fin d) :
    RealHermitianMatrix (Unit ⊕ Fin (d - 1)) →
      RealHermitianMatrix (Fin d) :=
  fun A =>
    ⟨Matrix.reindex (selectedCoordinateEquiv i).symm
      (selectedCoordinateEquiv i).symm A.1,
      isHermitian_reindex_equiv (selectedCoordinateEquiv i).symm A.1 A.2⟩

/-- Reindexing and unreindexing are mutually inverse. -/
theorem selectedCoordinateHermitian_unreindex_reindex
    {d : ℕ} (i : Fin d) (A : RealHermitianMatrix (Fin d)) :
    selectedCoordinateHermitianUnreindex i
      (selectedCoordinateHermitianReindex i A) = A := by
  apply Subtype.ext
  ext a b
  simp [selectedCoordinateHermitianReindex,
    selectedCoordinateHermitianUnreindex, Matrix.reindex_apply]

/-- The reverse inverse identity. -/
theorem selectedCoordinateHermitian_reindex_unreindex
    {d : ℕ} (i : Fin d)
    (A : RealHermitianMatrix (Unit ⊕ Fin (d - 1))) :
    selectedCoordinateHermitianReindex i
      (selectedCoordinateHermitianUnreindex i A) = A := by
  apply Subtype.ext
  ext a b
  simp [selectedCoordinateHermitianReindex,
    selectedCoordinateHermitianUnreindex, Matrix.reindex_apply]

/-- Selected-coordinate reindexing as a real-linear equivalence. -/
def selectedCoordinateHermitianLinearEquiv
    {d : ℕ} (i : Fin d) :
    RealHermitianMatrix (Fin d) ≃ₗ[ℝ]
      RealHermitianMatrix (Unit ⊕ Fin (d - 1)) where
  toFun := selectedCoordinateHermitianReindex i
  invFun := selectedCoordinateHermitianUnreindex i
  left_inv := selectedCoordinateHermitian_unreindex_reindex i
  right_inv := selectedCoordinateHermitian_reindex_unreindex i
  map_add' A B := by
    apply Subtype.ext
    ext a b
    rfl
  map_smul' c A := by
    apply Subtype.ext
    ext a b
    rfl

/-- The full arbitrary-selected-coordinate energy/tangent/complement split. -/
def selectedCoordinateEigenpairLinearEquiv
    {d : ℕ} (i : Fin d) :
    RealHermitianMatrix (Fin d) ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (selectedCoordinateHermitianLinearEquiv i).trans
    (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)))

/-- The selected energy coordinate is the real selected diagonal entry. -/
theorem selectedCoordinateEigenpairLinearEquiv_energy
    {d : ℕ} (i : Fin d) (A : RealHermitianMatrix (Fin d)) :
    (selectedCoordinateEigenpairLinearEquiv i A).1 = (A.1 i i).re := by
  change
    (A.1 ((selectedCoordinateEquiv i).symm (Sum.inl Unit.unit))
      ((selectedCoordinateEquiv i).symm (Sum.inl Unit.unit))).re =
        (A.1 i i).re
  rw [show (selectedCoordinateEquiv i).symm (Sum.inl Unit.unit) = i by
    apply (selectedCoordinateEquiv i).injective
    rw [(selectedCoordinateEquiv i).apply_symm_apply,
      selectedCoordinateEquiv_apply_selected]]

/-- The arbitrary-selected-coordinate split has exact two-sided reconstruction. -/
theorem selectedCoordinateEigenpairLinearEquiv_symm_apply_apply
    {d : ℕ} (i : Fin d) (A : RealHermitianMatrix (Fin d)) :
    (selectedCoordinateEigenpairLinearEquiv i).symm
      (selectedCoordinateEigenpairLinearEquiv i A) = A :=
  (selectedCoordinateEigenpairLinearEquiv i).symm_apply_apply A

/-- Conversely every energy/tangent/complement triple is recovered after
selected-coordinate reconstruction. -/
theorem selectedCoordinateEigenpairLinearEquiv_apply_symm_apply
    {d : ℕ} (i : Fin d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedCoordinateEigenpairLinearEquiv i
      ((selectedCoordinateEigenpairLinearEquiv i).symm y) = y :=
  (selectedCoordinateEigenpairLinearEquiv i).apply_symm_apply y

/-- Its dimension equality is automatic from the explicit real-linear
equivalence. -/
theorem finrank_selectedCoordinateEigenpair
    {d : ℕ} (i : Fin d) :
    Module.finrank ℝ (RealHermitianMatrix (Fin d)) =
      Module.finrank ℝ
        (EigenpairHermitianBlockCoordinates (Fin (d - 1))) :=
  LinearEquiv.finrank_eq (selectedCoordinateEigenpairLinearEquiv i)

/-- Unitary conjugation restricted to the real vector space of Hermitian
matrices. -/
def realHermitianUnitaryConjugationLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) :
    RealHermitianMatrix ι ≃ₗ[ℝ] RealHermitianMatrix ι where
  toFun A := ⟨Hᴴ * A.1 * H, isHermitian_unitaryConjugation H A.1 A.2⟩
  invFun A :=
    ⟨H * A.1 * Hᴴ, by
      change (H * A.1 * Hᴴ).IsHermitian
      simpa using isHermitian_unitaryConjugation Hᴴ A.1 A.2⟩
  left_inv A := by
    apply Subtype.ext
    change H * (Hᴴ * A.1 * H) * Hᴴ = A.1
    exact (unitaryConjugationLinearEquiv H hH).left_inv A.1
  right_inv A := by
    apply Subtype.ext
    change Hᴴ * (H * A.1 * Hᴴ) * H = A.1
    exact (unitaryConjugationLinearEquiv H hH).right_inv A.1
  map_add' A B := by
    apply Subtype.ext
    exact (unitaryConjugationLinearEquiv H hH).map_add A.1 B.1
  map_smul' c A := by
    apply Subtype.ext
    change Hᴴ * ((c : ℂ) • A.1) * H =
      (c : ℂ) • (Hᴴ * A.1 * H)
    exact (unitaryConjugationLinearEquiv H hH).map_smul (c : ℂ) A.1

/-- The fixed-point ordered-eigenline coordinate equivalence: first
conjugate by the unconditional phase-fixed Householder frame, then put its
selected coordinate first and split energy/tangent/complement blocks. -/
def orderedEigenlineSelectedCoordinateLinearEquiv
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    RealHermitianMatrix (Fin d) ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (realHermitianUnitaryConjugationLinearEquiv
      (orderedEigenlineHouseholderFrame d r p x)
      (orderedEigenlineHouseholderFrame_unitary_unconditional r p x)).trans
    (selectedCoordinateEigenpairLinearEquiv (ofLex p).1)

/-- At every fixed chart point the ordered Householder eigenpair coordinates
have exact two-sided reconstruction. -/
theorem orderedEigenlineSelectedCoordinate_symm_apply_apply
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (A : RealHermitianMatrix (Fin d)) :
    (orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm
      (orderedEigenlineSelectedCoordinateLinearEquiv r p x A) = A :=
  (orderedEigenlineSelectedCoordinateLinearEquiv r p x).symm_apply_apply A

end CoareaNative.BlockBand
