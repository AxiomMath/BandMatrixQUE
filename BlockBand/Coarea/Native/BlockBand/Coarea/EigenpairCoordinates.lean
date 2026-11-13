module

public import BlockBand.Coarea.Native.BlockBand.Coarea.RankSector
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Canonical eigenpair tangent coordinates

The finite-dimensional Jacobian computation in the density part of the eigenpair Jacobian
lemma.  At the canonical projective direction, the infinitesimal rotation of a block-diagonal
Hermitian matrix sends a complex tangent coordinate `z` to `(E I - B) z` in the lower-left
block.  Its complex determinant, and hence its real Jacobian density, is the spectral-gap
determinant.

The global change-of-variables formula, with the factor `π^(d-1)/(d-1)!` for the
probability-normalized projective measure, is not stated here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- A projective tangent vector at the canonical eigenvector, viewed as a block column. -/
def eigenpairTangentColumn {n : Type*} (z : n → ℂ) : Matrix n Unit ℂ :=
  fun i _ => z i

/-- The skew-adjoint infinitesimal rotation associated with the canonical projective
coordinate `z`.  The retained eigenvector coordinate (`Unit`) is placed first. -/
def eigenpairInfinitesimalRotation
    {n : Type*} [Fintype n] (z : n → ℂ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  Matrix.fromBlocks 0 (-(eigenpairTangentColumn z)ᴴ)
    (eigenpairTangentColumn z) 0

/-- The infinitesimal projective-coordinate rotation is skew-Hermitian. -/
theorem eigenpairInfinitesimalRotation_conjTranspose
    {n : Type*} [Fintype n] (z : n → ℂ) :
    (eigenpairInfinitesimalRotation z)ᴴ =
      -eigenpairInfinitesimalRotation z := by
  rw [eigenpairInfinitesimalRotation, Matrix.fromBlocks_conjTranspose]
  ext i j
  cases i <;> cases j <;> simp

/-- The canonical matrix with selected eigenvalue `E` and complementary block `B`. -/
def eigenpairCanonicalMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  Matrix.fromBlocks ((E : ℂ) • 1) 0 0 B

/-- The spectral-gap matrix governing the off-diagonal eigenvector differential. -/
def eigenpairGapMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  (E : ℂ) • 1 - B

/-- For a Hermitian complementary block, the spectral-gap matrix is Hermitian. -/
theorem eigenpairGapMatrix_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    (eigenpairGapMatrix E B).IsHermitian := by
  rw [Matrix.IsHermitian, eigenpairGapMatrix, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hB.eq]
  simp

/-- The lower-left block of the canonical commutator is exactly
`dK_off = (E - B) dz`.

Normalization: the selected direction is the first (`Unit`) block, the tangent
coordinate is a complex column `z`, and the commutator is `Ω K - K Ω`. -/
theorem eigenpair_commutator_lowerLeft
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) (i : n) :
    (eigenpairInfinitesimalRotation z * eigenpairCanonicalMatrix E B -
        eigenpairCanonicalMatrix E B * eigenpairInfinitesimalRotation z)
        (Sum.inr i) (Sum.inl Unit.unit) =
      (eigenpairGapMatrix E B *ᵥ z) i := by
  simp [eigenpairInfinitesimalRotation, eigenpairCanonicalMatrix,
    eigenpairGapMatrix, eigenpairTangentColumn, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.one_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp
  exact mul_comm _ _

/-- The complex-linear tangent map in the off-diagonal block. -/
def eigenpairOffdiagLinearMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) : (n → ℂ) →ₗ[ℂ] (n → ℂ) :=
  Matrix.toLin' (eigenpairGapMatrix E B)

/-- The off-diagonal tangent map acts by multiplication with `E I - B`. -/
theorem eigenpairOffdiagLinearMap_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) :
    eigenpairOffdiagLinearMap E B z = eigenpairGapMatrix E B *ᵥ z := by
  rfl

/-- The complex determinant of the canonical tangent map is the gap determinant. -/
theorem det_eigenpairOffdiagLinearMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    LinearMap.det (eigenpairOffdiagLinearMap E B) =
      (eigenpairGapMatrix E B).det := by
  exact LinearMap.det_toLin' _

/-- When no complementary eigenvalue equals `E`, the off-diagonal tangent map is the
linear equivalence induced by the invertible gap matrix. -/
def eigenpairOffdiagLinearEquiv
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) [Invertible (eigenpairGapMatrix E B)] :
    (n → ℂ) ≃ₗ[ℂ] (n → ℂ) :=
  Matrix.toLinearEquiv' (eigenpairGapMatrix E B) inferInstance

/-- The tangent linear equivalence has the same action as the off-diagonal linear map. -/
theorem eigenpairOffdiagLinearEquiv_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) [Invertible (eigenpairGapMatrix E B)]
    (z : n → ℂ) :
    eigenpairOffdiagLinearEquiv E B z = eigenpairGapMatrix E B *ᵥ z := by
  rfl

/-- The real Jacobian density of the complex-linear off-diagonal tangent map.

A complex-linear endomorphism with complex determinant `δ` has real Jacobian
`|δ|² = normSq δ`; this definition records precisely the density of the local
calculation in the eigenpair Jacobian lemma. -/
def eigenpairOffdiagJacobian
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) : ℝ :=
  Complex.normSq (eigenpairGapMatrix E B).det

/-- The canonical off-diagonal Jacobian density is nonnegative. -/
theorem eigenpairOffdiagJacobian_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    0 ≤ eigenpairOffdiagJacobian E B := by
  exact Complex.normSq_nonneg _

/-- For a Hermitian complementary block, the Jacobian density is the square of the
real gap determinant.  This is the precise finite-dimensional content of the
notation `det(B - E)²` of the paper (the sign change disappears after squaring). -/
theorem eigenpairOffdiagJacobian_eq_det_re_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    eigenpairOffdiagJacobian E B =
      (eigenpairGapMatrix E B).det.re ^ 2 := by
  let hgap := eigenpairGapMatrix_isHermitian E hB
  have hreal :
      (((eigenpairGapMatrix E B).det.re : ℝ) : ℂ) =
        (eigenpairGapMatrix E B).det := by
    rw [← Complex.conj_eq_iff_re]
    change star (eigenpairGapMatrix E B).det = (eigenpairGapMatrix E B).det
    rw [← Matrix.det_conjTranspose, hgap.eq]
  rw [eigenpairOffdiagJacobian, ← hreal, Complex.normSq_ofReal, pow_two]
  simp

end CoareaNative.BlockBand
