module

public import BlockBand.Native.CEH.ETH.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Deterministic Schur data for eigenpair coarea

This module fixes the algebraic conventions of the Schur data.  The
exposed pair is the left summand, the exterior is the right summand, and the
reconstruction vector has the sign `(v,-Tv)`.  The first result is
the exact kernel reconstruction used in the rank-preserving coarea formula.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- Exterior-to-pair transfer map `T = D⁻¹ C`. -/
def schurTransfer
    {m n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D] :
    Matrix n m α :=
  ⅟D * C

/-- Reconstruction map `L v = (v,-Tv)` in the pair/exterior splitting. -/
def schurReconstruction
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq n] [CommRing α]
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D]
    (v : m → α) : m ⊕ n → α :=
  v ⊕ᵥ (-((schurTransfer C D) *ᵥ v))

/-- The Schur reconstruction retains the pair component and is therefore
injective. -/
theorem schurReconstruction_injective
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq n] [CommRing α]
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D] :
    Function.Injective (schurReconstruction C D) := by
  intro v w hvw
  funext i
  exact congrFun hvw (Sum.inl i)

/-- Positive clock matrix `𝒟 = I + TᴴT`. -/
def schurClock
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) : Matrix m m ℂ :=
  1 + Tᴴ * T

/-- The Schur graph identity in the paper's named notation. -/
theorem fromBlocks_mulVec_schurReconstruction
    {m n α : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D]
    (v : m → α) :
    Matrix.fromBlocks A B C D *ᵥ schurReconstruction C D v =
      ((A - B * ⅟D * C) *ᵥ v) ⊕ᵥ (0 : n → α) := by
  unfold schurReconstruction schurTransfer
  exact fromBlocks_mulVec_schurGraph A B C D v

/-- Kernel reconstruction: a null vector of the Schur complement gives a
null vector of the full block matrix. -/
theorem schurReconstruction_mem_ker
    {m n α : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α)
    (C : Matrix n m α) (D : Matrix n n α) [Invertible D]
    (v : m → α) (hv : (A - B * ⅟D * C) *ᵥ v = 0) :
    Matrix.fromBlocks A B C D *ᵥ schurReconstruction C D v = 0 := by
  rw [fromBlocks_mulVec_schurReconstruction A B C D v, hv]
  ext i
  cases i <;> rfl

/-- The Schur clock is positive semidefinite. -/
theorem schurClock_posSemidef
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    (schurClock T).PosSemidef := by
  unfold schurClock
  exact Matrix.PosSemidef.one.add (Matrix.posSemidef_conjTranspose_mul_self T)

/-- The identity contribution makes the Schur clock strictly positive. -/
theorem schurClock_posDef
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    (schurClock T).PosDef := by
  unfold schurClock
  exact Matrix.PosDef.one.add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self T)

/-- In particular, the Schur clock is invertible. -/
theorem schurClock_isUnit
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    IsUnit (schurClock T) :=
  (schurClock_posDef T).isUnit

/-- The clock quadratic form is exactly the squared mass of the reconstructed
Schur-graph vector.  This is the deterministic identity behind
the clock reconstruction identity. -/
theorem dotProduct_schurReconstruction_eq_schurClock
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) :
    star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v))) =
      star v ⬝ᵥ (schurClock T *ᵥ v) := by
  rw [show star (v ⊕ᵥ (-(T *ᵥ v))) =
      (star v ⊕ᵥ star (-(T *ᵥ v))) by
    ext i
    cases i <;> rfl]
  rw [sumElim_dotProduct_sumElim]
  simp [schurClock, Matrix.add_mulVec, Matrix.mulVec_mulVec,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

/-- Every nonzero pair direction has a strictly positive clock. -/
theorem schurClock_quadratic_pos
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) {v : m → ℂ} (hv : v ≠ 0) :
    0 < star v ⬝ᵥ (schurClock T *ᵥ v) :=
  (schurClock_posDef T).dotProduct_mulVec_pos hv

/-- Consequently, the reconstructed Schur-graph vector of a nonzero pair
direction has strictly positive squared mass. -/
theorem dotProduct_schurReconstruction_pos
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) {v : m → ℂ} (hv : v ≠ 0) :
    0 < star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v))) := by
  rw [dotProduct_schurReconstruction_eq_schurClock]
  exact schurClock_quadratic_pos T hv

end CEHNative.BlockBand
