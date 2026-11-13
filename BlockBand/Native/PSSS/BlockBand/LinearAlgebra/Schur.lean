module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Schur-complement resolvent block

The upper-left block of the inverse of a block matrix is the inverse of the Schur complement of
its lower-right block. This is Mathlib's Schur-complement inverse formula, in the convention of
the projected Wegner lemma: the exposed Gaussian block is the upper-left block and the exterior is
the lower-right block.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open Matrix

/-- Schur complement of the lower-right exterior block. -/
def schurComplement₂₂
    {m n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D] :
    Matrix m m α :=
  A - B * ⅟D * C

/-- The graph vector used in the Schur argument is sent to the exposed Schur
component and zero in the exterior component. -/
theorem fromBlocks_mulVec_schurGraph
    {m n α : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D]
    (x : m → α) :
    Matrix.fromBlocks A B C D *ᵥ
        (x ⊕ᵥ (-((⅟D * C) *ᵥ x))) =
      ((A - B * ⅟D * C) *ᵥ x) ⊕ᵥ (0 : n → α) := by
  ext i
  cases i with
  | inl i =>
      simp [Matrix.fromBlocks_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.add_mulVec,
        Matrix.mul_assoc, sub_eq_add_neg]
  | inr i =>
      simp [Matrix.fromBlocks_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_neg, Matrix.mul_assoc]

/-- The exposed block of the full inverse is the inverse of the Schur
complement. -/
theorem invOf_fromBlocks_submatrix₁₁
    {m n α : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α)
    [Invertible D] [Invertible (A - B * ⅟D * C)]
    [Invertible (Matrix.fromBlocks A B C D)] :
    (⅟(Matrix.fromBlocks A B C D)).submatrix Sum.inl Sum.inl =
      ⅟(A - B * ⅟D * C) := by
  ext i j
  rw [Matrix.invOf_fromBlocks₂₂_eq A B C D]
  rfl

end PSSSNative.BlockBand
