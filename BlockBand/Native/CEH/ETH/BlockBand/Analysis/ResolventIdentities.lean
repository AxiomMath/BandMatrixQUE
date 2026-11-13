module

public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.PositiveResolvent

/-!
# Finite Hermitian resolvent identities

This module records the paper's resolvent convention
`G_A(z) = (z I - A)⁻¹`.  Away from the real axis it proves invertibility, the
first resolvent identity, compatibility with conjugate transpose, and the
finite-dimensional Ward identity
`G Gᴴ = -(Im z)⁻¹ Im G`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand

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

/-- Determinant form of nonreal resolvent invertibility. -/
theorem isUnit_det_resolventPencil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (z • (1 : Matrix ι ι ℂ) - A).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_resolventPencil A hA hz)

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

/-- Finite-dimensional Ward identity in the paper's sign convention. -/
theorem matrixResolvent_mul_conjTranspose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    matrixResolvent A z * (matrixResolvent A z)ᴴ =
      (-(z.im)⁻¹ : ℂ) • matrixImaginaryPart (matrixResolvent A z) := by
  have hstar : (star z).im ≠ 0 := by simpa using hz
  have hres := matrixResolvent_sub A hA hz hstar
  rw [← matrixResolvent_conjTranspose A hA z] at hres
  have hdiff : star z - z = (-2 * z.im * Complex.I : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [hdiff] at hres
  rw [matrixImaginaryPart]
  rw [show matrixResolvent A z - (matrixResolvent A z)ᴴ =
      (-2 * z.im * Complex.I : ℂ) •
        (matrixResolvent A z * (matrixResolvent A z)ᴴ) by
      exact hres]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [hz]
  rw [Complex.I_sq]
  norm_num [one_div, hz]

/-- Paper-facing package of the first resolvent identity, adjoint identity,
and Ward identity.  Both spectral parameters are explicitly nonreal. -/
theorem finiteResolventIdentities
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (matrixResolvent A z - matrixResolvent A w =
        (w - z) • (matrixResolvent A z * matrixResolvent A w)) ∧
      ((matrixResolvent A z)ᴴ = matrixResolvent A (star z)) ∧
      (matrixResolvent A z * (matrixResolvent A z)ᴴ =
        (-(z.im)⁻¹ : ℂ) • matrixImaginaryPart (matrixResolvent A z)) :=
  ⟨matrixResolvent_sub A hA hz hw,
    matrixResolvent_conjTranspose A hA z,
    matrixResolvent_mul_conjTranspose A hA hz⟩

end CEHNative.BlockBand
