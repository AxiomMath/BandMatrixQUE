module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic

/-!
# Positivity of an absorbed resolvent

This file supplies the deterministic matrix identity used twice in the
projected-Wegner/passive-log repair.  We use the Hermitian matrix-valued
imaginary part

`Im M = (2 i)⁻¹ (M - Mᴴ)`.

For an invertible matrix the exact identity is

`-Im (M⁻¹) = (M⁻¹)ᴴ (Im M) M⁻¹`.

Consequently a positive-semidefinite absorber makes the negative imaginary
part of its resolvent positive semidefinite.  No simultaneous
diagonalization is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- Hermitian matrix-valued imaginary part, `(-i/2)(M - Mᴴ)`. -/
def matrixImaginaryPart {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I / 2) • (M - Mᴴ)

/-- The matrix imaginary part is Hermitian. -/
theorem matrixImaginaryPart_isHermitian {n : Type*} (M : Matrix n n ℂ) :
    (matrixImaginaryPart M).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [matrixImaginaryPart]
  ring

/-- A Hermitian real part plus `i` times a Hermitian absorber has imaginary
part exactly the absorber. -/
theorem matrixImaginaryPart_add_I_smul
    {n : Type*} (A Γ : Matrix n n ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.IsHermitian) :
    matrixImaginaryPart (A + Complex.I • Γ) = Γ := by
  ext i j
  simp [matrixImaginaryPart, hA.eq, hΓ.eq]
  ring_nf
  rw [Complex.I_sq]
  simp

private theorem quadraticForm_star
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (Aᴴ *ᵥ v) = star (star v ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [star_star]
  exact Matrix.star_dotProduct _ _

/-- A finite complex matrix whose Hermitian imaginary part is positive
definite is invertible. -/
theorem isUnit_of_matrixImaginaryPart_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ}
    (hM : (matrixImaginaryPart M).PosDef) :
    IsUnit M := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hne
  have hv : M *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hpos := hM.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  have hquad : star (x - y) ⬝ᵥ (M *ᵥ (x - y)) = 0 := by
    rw [hv, dotProduct_zero]
  have hquadStar : star (x - y) ⬝ᵥ (Mᴴ *ᵥ (x - y)) = 0 := by
    rw [quadraticForm_star, hquad]
    exact star_zero ℂ
  have hzero :
      star (x - y) ⬝ᵥ
        (matrixImaginaryPart M *ᵥ (x - y)) = 0 := by
    rw [matrixImaginaryPart, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.sub_mulVec, dotProduct_sub, hquad, hquadStar, sub_self,
      smul_zero]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- A Hermitian matrix plus `i` times a positive-definite Hermitian absorber
is invertible. -/
theorem isUnit_add_I_smul_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A Γ : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hΓ : Γ.PosDef) :
    IsUnit (A + Complex.I • Γ) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rwa [matrixImaginaryPart_add_I_smul A Γ hA hΓ.isHermitian]

/-- Imaginary part commutes with the unnormalized matrix trace. -/
theorem trace_matrixImaginaryPart
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (matrixImaginaryPart M).trace = ((M.trace).im : ℂ) := by
  rw [matrixImaginaryPart, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_conjTranspose]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Trace form with the negative-imaginary convention: `Tr(-Im M) = -Im Tr M`. -/
theorem trace_neg_matrixImaginaryPart
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (-matrixImaginaryPart M).trace = ((-(M.trace).im : ℝ) : ℂ) := by
  rw [Matrix.trace_neg, trace_matrixImaginaryPart]
  simp

/-- Absorbed inverse identity:
`-Im (M⁻¹) = (M⁻¹)ᴴ (Im M) M⁻¹`. -/
theorem neg_matrixImaginaryPart_nonsing_inv
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : IsUnit M.det) :
    -matrixImaginaryPart M⁻¹ =
      M⁻¹ᴴ * matrixImaginaryPart M * M⁻¹ := by
  rw [matrixImaginaryPart, matrixImaginaryPart]
  rw [Matrix.conjTranspose_nonsing_inv]
  have hMH : IsUnit Mᴴ.det := by
    exact (Matrix.isUnit_iff_isUnit_det Mᴴ).mp
      ((Matrix.isUnit_conjTranspose M).mpr
        ((Matrix.isUnit_iff_isUnit_det M).mpr hM))
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_neg]
  congr 1
  rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [M.mul_nonsing_inv hM, Matrix.mul_one]
  rw [← Matrix.mul_assoc Mᴴ⁻¹ Mᴴ M⁻¹, Mᴴ.nonsing_inv_mul hMH, Matrix.one_mul]
  module

/-- Positivity consequence of the absorbed inverse identity. -/
theorem neg_matrixImaginaryPart_nonsing_inv_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : IsUnit M.det)
    (him : (matrixImaginaryPart M).PosSemidef) :
    (-matrixImaginaryPart M⁻¹).PosSemidef := by
  rw [neg_matrixImaginaryPart_nonsing_inv M hM]
  exact him.conjTranspose_mul_mul_same M⁻¹

end PSSSNative.BlockBand
