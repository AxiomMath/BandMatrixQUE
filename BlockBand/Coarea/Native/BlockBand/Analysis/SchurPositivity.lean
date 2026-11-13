module

public import BlockBand.Coarea.Native.BlockBand.Analysis.PositiveResolvent
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.Schur

/-!
# Positivity of Schur-complement absorption

If the imaginary part of a block matrix dominates `η I`, with `η ≥ 0`,
then the imaginary part of the Schur complement over an invertible exterior
block also dominates `η I`.

The proof evaluates the full quadratic form on the Schur graph vector
`(x, -D⁻¹ C x)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped ComplexOrder

private theorem quadraticForm_conjTranspose
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (Mᴴ *ᵥ v) =
      star (star v ⬝ᵥ (M *ᵥ v)) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [star_star]
  exact Matrix.star_dotProduct _ _

private theorem quadraticForm_matrixImaginaryPart
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (matrixImaginaryPart M *ᵥ v) =
      (-Complex.I / 2) •
        ((star v ⬝ᵥ (M *ᵥ v)) -
          star (star v ⬝ᵥ (M *ᵥ v))) := by
  rw [matrixImaginaryPart, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.sub_mulVec, dotProduct_sub, quadraticForm_conjTranspose]

private theorem dotProduct_sum_elim
    {m n : Type*} [Fintype m] [Fintype n]
    (x x' : m → ℂ) (y y' : n → ℂ) :
    (x ⊕ᵥ y) ⬝ᵥ (x' ⊕ᵥ y') =
      (x ⬝ᵥ x') + (y ⬝ᵥ y') := by
  simp [dotProduct, Fintype.sum_sum_type]

private theorem star_sum_elim
    {m n : Type*} (x : m → ℂ) (y : n → ℂ) :
    star (x ⊕ᵥ y) = star x ⊕ᵥ star y := by
  ext i
  cases i <;> rfl

/-- If the imaginary part of a block matrix dominates `η I`, then the
imaginary part of its Schur complement over an invertible exterior block also
dominates `η I`.

The hypothesis and conclusion are the exact Loewner-order formulation:
`Im M - η I` and `Im S - η I` are positive semidefinite. The restriction
`η ≥ 0` pays for the exterior component of the Schur graph vector. -/
theorem schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) [Invertible D]
    {η : ℝ} (hη : 0 ≤ η)
    (hfull :
      (matrixImaginaryPart (Matrix.fromBlocks A B C D) -
        (η : ℂ) •
          (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef) :
    (matrixImaginaryPart (schurComplement₂₂ A B C D) -
      (η : ℂ) • (1 : Matrix m m ℂ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact
      (matrixImaginaryPart_isHermitian _).sub
        (Matrix.isHermitian_one.smul (RCLike.conj_ofReal η))
  · intro x
    let y : n → ℂ := -((⅟D * C) *ᵥ x)
    let z : Sum m n → ℂ := x ⊕ᵥ y
    have hact :
        Matrix.fromBlocks A B C D *ᵥ z =
          (schurComplement₂₂ A B C D *ᵥ x) ⊕ᵥ
            (0 : n → ℂ) := by
      simpa [z, y, schurComplement₂₂] using
        fromBlocks_mulVec_schurGraph A B C D x
    have hq :
        star z ⬝ᵥ
            (matrixImaginaryPart
              (Matrix.fromBlocks A B C D) *ᵥ z) =
          star x ⬝ᵥ
            (matrixImaginaryPart
              (schurComplement₂₂ A B C D) *ᵥ x) := by
      rw [quadraticForm_matrixImaginaryPart,
        quadraticForm_matrixImaginaryPart, hact]
      rw [star_sum_elim, dotProduct_sum_elim]
      simp
    have hbase := hfull.dotProduct_mulVec_nonneg z
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, Matrix.one_mulVec, hq] at hbase
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, Matrix.one_mulVec]
    have hzNorm :
        star z ⬝ᵥ z =
          (star x ⬝ᵥ x) + (star y ⬝ᵥ y) := by
      change
        star (x ⊕ᵥ y) ⬝ᵥ (x ⊕ᵥ y) =
          (star x ⬝ᵥ x) + (star y ⬝ᵥ y)
      rw [star_sum_elim, dotProduct_sum_elim]
    rw [hzNorm] at hbase
    have hy : 0 ≤ (η : ℂ) • (star y ⬝ᵥ y) := by
      exact smul_nonneg (by simpa using hη) (by simp)
    have heq :
        (star x ⬝ᵥ
              (matrixImaginaryPart
                (schurComplement₂₂ A B C D) *ᵥ x) -
            (η : ℂ) •
              ((star x ⬝ᵥ x) + (star y ⬝ᵥ y))) +
            (η : ℂ) • (star y ⬝ᵥ y) =
          star x ⬝ᵥ
              (matrixImaginaryPart
                (schurComplement₂₂ A B C D) *ᵥ x) -
            (η : ℂ) • (star x ⬝ᵥ x) := by
      simp only [smul_eq_mul]
      ring
    rw [← heq]
    exact add_nonneg hbase hy

end CoareaNative.BlockBand
