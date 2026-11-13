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

namespace ERNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- Hermitian matrix-valued imaginary part `(M - Mᴴ)/(2i)`, with the sign
convention of the paper. -/
def matrixImaginaryPart {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I / 2) • (M - Mᴴ)

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

end ERNative.BlockBand
