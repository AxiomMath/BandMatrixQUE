module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianDiscriminant
public import BlockBand.Coarea.Native.BlockBand.Spectral.Ordered
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# Real coordinates for complex Hermitian matrices

A complex Hermitian `d × d` matrix has `d` real diagonal coordinates and two
real coordinates for each strict upper-triangular entry.  This module constructs
that coordinate system explicitly and proves that reconstruction and coordinate
extraction are mutually inverse real-linear maps.

These coordinates are used to expand the characteristic matrix discriminant as
a real multivariate polynomial, to which the null-locus theorem for real
polynomials applies.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- An index in the strict upper triangle of a `d × d` matrix. -/
abbrev StrictUpperIndex (d : ℕ) :=
  {ij : Fin d × Fin d // ij.1 < ij.2}

/-- Real coordinates of a complex Hermitian matrix: diagonal, real upper
triangle, and imaginary upper triangle. -/
abbrev HermitianCoordinate (d : ℕ) :=
  Fin d ⊕ (StrictUpperIndex d ⊕ StrictUpperIndex d)

/-- The complex number stored at one strict upper-triangular position. -/
def hermitianUpperEntry {d : ℕ}
    (x : HermitianCoordinate d → ℝ) (ij : StrictUpperIndex d) : ℂ :=
  (x (.inr (.inl ij)) : ℂ) + (x (.inr (.inr ij)) : ℂ) * Complex.I

/-- Reconstruct the full matrix from diagonal and strict-upper coordinates.
The lower triangle is filled by complex conjugation. -/
def hermitianMatrixOfCoordinates {d : ℕ}
    (x : HermitianCoordinate d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    if hEq : i = j then (x (.inl i) : ℂ)
    else if hLt : i < j then
      hermitianUpperEntry x ⟨(i, j), hLt⟩
    else
      star (hermitianUpperEntry x
        ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)⟩)

/-- Reconstruction always produces a Hermitian matrix. -/
theorem hermitianMatrixOfCoordinates_isHermitian {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    (hermitianMatrixOfCoordinates x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hEq : i = j
  · subst j
    simp [hermitianMatrixOfCoordinates]
  · by_cases hLt : i < j
    · have hNot : ¬j < i := not_lt_of_ge (le_of_lt hLt)
      simp [Matrix.conjTranspose_apply, hermitianMatrixOfCoordinates, hEq, hLt,
        Ne.symm hEq, hNot]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)
      simp [Matrix.conjTranspose_apply, hermitianMatrixOfCoordinates, hEq, hLt,
        Ne.symm hEq, hji]

/-- Hermitian reconstruction, packaged in the project-wide subtype. -/
def hermitianOfCoordinates {d : ℕ}
    (x : HermitianCoordinate d → ℝ) : HermitianMatrix (Fin d) :=
  ⟨hermitianMatrixOfCoordinates x, hermitianMatrixOfCoordinates_isHermitian x⟩

/-- Extract the diagonal and strict-upper real/imaginary coordinates of a
Hermitian matrix. -/
def coordinatesOfHermitian {d : ℕ}
    (A : HermitianMatrix (Fin d)) : HermitianCoordinate d → ℝ
  | .inl i => (A.1 i i).re
  | .inr (.inl ij) => (A.1 ij.1.1 ij.1.2).re
  | .inr (.inr ij) => (A.1 ij.1.1 ij.1.2).im

/-- Coordinate extraction after reconstruction is the identity. -/
theorem coordinatesOfHermitian_hermitianOfCoordinates {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    coordinatesOfHermitian (hermitianOfCoordinates x) = x := by
  funext c
  rcases c with i | c
  · simp [coordinatesOfHermitian, hermitianOfCoordinates,
      hermitianMatrixOfCoordinates]
  · rcases c with ij | ij
    · change (hermitianMatrixOfCoordinates x ij.1.1 ij.1.2).re =
        x (.inr (.inl ij))
      simp [hermitianMatrixOfCoordinates, hermitianUpperEntry,
        ij.property.ne, ij.property]
    · change (hermitianMatrixOfCoordinates x ij.1.1 ij.1.2).im =
        x (.inr (.inr ij))
      simp [hermitianMatrixOfCoordinates, hermitianUpperEntry,
        ij.property.ne, ij.property]

/-- Reconstruction after coordinate extraction is the original Hermitian
matrix. -/
theorem hermitianOfCoordinates_coordinatesOfHermitian {d : ℕ}
    (A : HermitianMatrix (Fin d)) :
    hermitianOfCoordinates (coordinatesOfHermitian A) = A := by
  apply Subtype.ext
  ext i j
  by_cases hEq : i = j
  · subst j
    simpa [hermitianOfCoordinates, hermitianMatrixOfCoordinates,
      coordinatesOfHermitian] using A.property.coe_re_apply_self i
  · by_cases hLt : i < j
    · simp only [hermitianOfCoordinates, hermitianMatrixOfCoordinates,
        hEq, hLt, ↓reduceDIte, coordinatesOfHermitian, hermitianUpperEntry]
      apply Complex.ext <;> simp
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)
      simp only [hermitianOfCoordinates, hermitianMatrixOfCoordinates, hEq,
        hLt, ↓reduceDIte, coordinatesOfHermitian, hermitianUpperEntry]
      rw [← A.property.apply i j]
      congr 1
      apply Complex.ext <;> simp

/-- Explicit equivalence between coordinate space and finite complex Hermitian
matrices.  The forward map is real-linear after forgetting the Hermitian proof;
that linear map is exposed separately below. -/
def hermitianCoordinatesEquiv (d : ℕ) :
    (HermitianCoordinate d → ℝ) ≃ HermitianMatrix (Fin d) where
  toFun := hermitianOfCoordinates
  invFun := coordinatesOfHermitian
  left_inv := coordinatesOfHermitian_hermitianOfCoordinates
  right_inv := hermitianOfCoordinates_coordinatesOfHermitian

/-- Reconstruction as a real-linear map into the ambient complex matrix
space.  Its range is exactly the Hermitian matrices by the equivalence above. -/
def hermitianCoordinatesLinearMap (d : ℕ) :
    (HermitianCoordinate d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ where
  toFun := hermitianMatrixOfCoordinates
  map_add' x y := by
    ext i j
    by_cases hEq : i = j
    · subst j
      simp [hermitianMatrixOfCoordinates]
    · by_cases hLt : i < j
      · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry, hEq, hLt]
        ring
      · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry, hEq, hLt]
        ring
  map_smul' r x := by
    ext i j
    by_cases hEq : i = j
    · subst j
      simp [hermitianMatrixOfCoordinates]
    · by_cases hLt : i < j
      · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry, hEq, hLt,
          smul_eq_mul]
        ring
      · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry, hEq, hLt,
          smul_eq_mul]
        ring

/-- The coordinate equivalence has the expected forward map. -/
theorem hermitianCoordinatesEquiv_apply (d : ℕ)
    (x : HermitianCoordinate d → ℝ) :
    hermitianCoordinatesEquiv d x = hermitianOfCoordinates x := rfl

/-- The inverse coordinate equivalence is coordinate extraction. -/
theorem hermitianCoordinatesEquiv_symm_apply (d : ℕ)
    (A : HermitianMatrix (Fin d)) :
    (hermitianCoordinatesEquiv d).symm A = coordinatesOfHermitian A := rfl

/-- The real-linear reconstruction map parametrizes exactly the Hermitian
matrices inside the ambient complex matrix space. -/
theorem range_hermitianCoordinatesLinearMap (d : ℕ) :
    Set.range (hermitianCoordinatesLinearMap d) =
      {A : Matrix (Fin d) (Fin d) ℂ | A.IsHermitian} := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact hermitianMatrixOfCoordinates_isHermitian x
  · intro hA
    let H : HermitianMatrix (Fin d) := ⟨A, hA⟩
    refine ⟨coordinatesOfHermitian H, ?_⟩
    have h := congrArg Subtype.val
      (hermitianOfCoordinates_coordinatesOfHermitian H)
    exact h

/-- Canonical reindexing of Hermitian coordinates by a finite ordinal.  This
is the index equivalence needed to feed a coordinate polynomial to
`volume_mvPolynomial_zeroSet`. -/
noncomputable def hermitianCoordinateEquivFin (d : ℕ) :
    HermitianCoordinate d ≃ Fin (Fintype.card (HermitianCoordinate d)) :=
  Fintype.equivFin _

/-- Real coordinate functions, reindexed into the `Fin n → ℝ` convention used
by the polynomial zero-set nullity theorem. -/
noncomputable def hermitianCoordinateFunctionsLinearEquiv (d : ℕ) :
    (HermitianCoordinate d → ℝ) ≃ₗ[ℝ]
      (Fin (Fintype.card (HermitianCoordinate d)) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (hermitianCoordinateEquivFin d).symm

end CoareaNative.BlockBand
