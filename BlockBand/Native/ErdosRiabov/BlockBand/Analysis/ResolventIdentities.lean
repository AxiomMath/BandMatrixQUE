module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.PositiveResolvent

/-!
# Finite Hermitian resolvent identities

This module records the paper's resolvent convention
`G_A(z) = (z I - A)⁻¹`.  Away from the real axis it proves invertibility, the
first resolvent identity and compatibility with conjugate transpose.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- The resolvent convention of the paper, `G_A(z) = (z I - A)⁻¹`. -/
def matrixResolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (z • (1 : Matrix ι ι ℂ) - A)⁻¹

/-- The matrix imaginary part of the shifted Hermitian pencil is the scalar
imaginary part times the identity. -/
theorem matrixImaginaryPart_smul_one_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (z : ℂ) :
    matrixImaginaryPart (z • (1 : Matrix ι ι ℂ) - A) =
      z.im • (1 : Matrix ι ι ℂ) := by
  have hreal :
      ((z.re : ℂ) • (1 : Matrix ι ι ℂ) - A).IsHermitian :=
    Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re) |>.sub hA
  have him :
      (z.im • (1 : Matrix ι ι ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.im)
  rw [show z • (1 : Matrix ι ι ℂ) - A =
      ((z.re : ℂ) • (1 : Matrix ι ι ℂ) - A) +
        Complex.I • (z.im • (1 : Matrix ι ι ℂ)) by
    ext i j
    simp [Complex.ext_iff]
    constructor <;> ring]
  exact matrixImaginaryPart_add_I_smul _ _ hreal him

/-- A Hermitian resolvent pencil is invertible at every nonreal spectral
parameter. -/
theorem isUnit_resolventPencil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (z • (1 : Matrix ι ι ℂ) - A) := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hpos : (matrixImaginaryPart
        (-(z • (1 : Matrix ι ι ℂ) - A))).PosDef := by
      rw [show matrixImaginaryPart
        (-(z • (1 : Matrix ι ι ℂ) - A)) =
          (-z.im) • (1 : Matrix ι ι ℂ) by
        rw [show matrixImaginaryPart
          (-(z • (1 : Matrix ι ι ℂ) - A)) =
            -matrixImaginaryPart (z • (1 : Matrix ι ι ℂ) - A) by
          ext i j
          simp [matrixImaginaryPart]
          ring]
        rw [matrixImaginaryPart_smul_one_sub A hA z]
        simp]
      exact Matrix.PosDef.one.smul (neg_pos.mpr hzneg)
    have hu : IsUnit (-(z • (1 : Matrix ι ι ℂ) - A)) :=
      isUnit_of_matrixImaginaryPart_posDef hpos
    exact (IsUnit.neg_iff _).mp hu
  · apply isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_smul_one_sub A hA z]
    exact Matrix.PosDef.one.smul hzpos

/-- First resolvent identity in the convention `G(z)=(zI-A)⁻¹`. -/
theorem matrixResolvent_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    matrixResolvent A z - matrixResolvent A w =
      (w - z) • (matrixResolvent A z * matrixResolvent A w) := by
  unfold matrixResolvent
  rw [Matrix.inv_sub_inv]
  · rw [show w • (1 : Matrix ι ι ℂ) - A -
        (z • (1 : Matrix ι ι ℂ) - A) =
      (w - z) • (1 : Matrix ι ι ℂ) by
        ext i j
        simp
        ring]
    simp
  · exact ⟨fun _ => isUnit_resolventPencil A hA hw,
      fun _ => isUnit_resolventPencil A hA hz⟩

/-- Conjugate-transpose compatibility of the Hermitian resolvent. -/
theorem matrixResolvent_conjTranspose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (z : ℂ) :
    (matrixResolvent A z)ᴴ = matrixResolvent A (star z) := by
  unfold matrixResolvent
  rw [Matrix.conjTranspose_nonsing_inv]
  rw [show (z • (1 : Matrix ι ι ℂ) - A)ᴴ =
      (star z) • (1 : Matrix ι ι ℂ) - A by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq]
    simp]

end ERNative.BlockBand
