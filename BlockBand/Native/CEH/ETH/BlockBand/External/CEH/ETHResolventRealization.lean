module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHDeterministicExtraction
public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.PositiveResolvent

/-!
# Resolvent realization of the CEH spectral kernel

This module closes the deterministic resolvent residual following
`ETHDeterministicExtraction`.  For the repository convention
`(A - z I)⁻¹`, an orthonormal eigenfamily of the Hermitian matrix `A`
identifies the positive spectral kernel at `z = x + iη` with the matrix
imaginary part of the resolvent.  The only analytic hypothesis is
`η > 0`, which keeps every scalar spectral denominator nonzero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-- The unitary matrix whose columns are the supplied CEH eigenvectors. -/
private def eigenvectorMatrix {N : ℕ} (u : Fin N → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun a i => u i a

/-- A square orthonormal eigenfamily resolves the identity into its rank-one
projectors. -/
theorem sum_spectralProjector_eq_one {N : ℕ}
    {A : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily A lam u) :
    ∑ i, spectralProjector u i = 1 := by
  classical
  let U := eigenvectorMatrix u
  have hUstarU : Uᴴ * U = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, eigenvectorMatrix,
      Matrix.one_apply]
    simpa [dotProduct] using hfamily.1 i j
  have hUUstar : U * Uᴴ = 1 := (mul_eq_one_comm.mp hUstarU)
  rw [← hUUstar]
  ext a b
  simp only [Matrix.sum_apply, spectralProjector, Matrix.mul_apply, U,
    eigenvectorMatrix, Matrix.conjTranspose_apply, Matrix.vecMulVec]
  rfl

/-- The shifted matrix acts diagonally on every supplied eigenvector. -/
private theorem shifted_mulVec_eigenvector {N : ℕ}
    {A : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily A lam u)
    (z : ℂ) (i : Fin N) :
    (A - z • (1 : LocalETHMatrix N)) *ᵥ u i =
      ((lam i : ℂ) - z) • u i := by
  rw [Matrix.sub_mulVec, hfamily.2 i, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext a
  simp
  ring

/-- Spectral expansion of the shifted inverse.  Positive imaginary
height is used only to show the scalar factors `λᵢ - (x+iη)` are nonzero. -/
theorem actualResolvent_eq_sum_spectralProjector {N : ℕ}
    {A : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily A lam u)
    (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (A - ((x : ℂ) + (eta : ℂ) * Complex.I) •
        (1 : LocalETHMatrix N))⁻¹ =
      ∑ i, (((lam i : ℂ) - ((x : ℂ) + (eta : ℂ) * Complex.I))⁻¹) •
        spectralProjector u i := by
  classical
  let z : ℂ := (x : ℂ) + (eta : ℂ) * Complex.I
  let M : LocalETHMatrix N := A - z • 1
  let R : LocalETHMatrix N :=
    ∑ i, (((lam i : ℂ) - z)⁻¹) • spectralProjector u i
  have hscalar (i : Fin N) : (lam i : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [z] at him
    linarith
  have hMR : M * R = 1 := by
    simp only [R, Matrix.mul_sum]
    simp_rw [Matrix.mul_smul]
    rw [← sum_spectralProjector_eq_one hfamily]
    apply Finset.sum_congr rfl
    intro i _
    rw [spectralProjector, Matrix.mul_vecMulVec,
      show M *ᵥ u i = ((lam i : ℂ) - z) • u i by
      simpa [M] using shifted_mulVec_eigenvector hfamily z i]
    ext a b
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp [hscalar i]
  have hMunit : IsUnit M := by
    exact isUnit_iff_exists_inv.mpr ⟨R, hMR⟩
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMunit
  change M⁻¹ = R
  calc
    M⁻¹ = M⁻¹ * 1 := by rw [Matrix.mul_one]
    _ = M⁻¹ * (M * R) := by rw [hMR]
    _ = (M⁻¹ * M) * R := by rw [Matrix.mul_assoc]
    _ = R := by rw [M.nonsing_inv_mul hMdet, Matrix.one_mul]

/-- Rank-one spectral projectors are Hermitian. -/
private theorem spectralProjector_isHermitian {N : ℕ}
    (u : Fin N → Fin N → ℂ) (i : Fin N) :
    (spectralProjector u i).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  simp [spectralProjector, Matrix.vecMulVec]
  ring

/-- Matrix imaginary part is additive over a finite sum. -/
private theorem matrixImaginaryPart_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → LocalETHMatrix N) :
    matrixImaginaryPart (∑ i, f i) = ∑ i, matrixImaginaryPart (f i) := by
  classical
  have hct : (∑ i, f i)ᴴ = ∑ i, (f i)ᴴ := by
    simpa using Matrix.conjTranspose_sum Finset.univ f
  have hsub :
      (∑ i, f i) - ∑ i, (f i)ᴴ = ∑ i, (f i - (f i)ᴴ) := by
    simp
  have hsmul :
      (-Complex.I / 2) • (∑ i, (f i - (f i)ᴴ)) =
        ∑ i, (-Complex.I / 2) • (f i - (f i)ᴴ) := by
    exact Finset.smul_sum
  unfold matrixImaginaryPart
  rw [hct, hsub, hsmul]

/-- On a Hermitian direction, matrix imaginary part extracts the scalar
imaginary part. -/
private theorem matrixImaginaryPart_smul_isHermitian {N : ℕ}
    (c : ℂ) (P : LocalETHMatrix N) (hP : P.IsHermitian) :
    matrixImaginaryPart (c • P) = (c.im : ℂ) • P := by
  ext a b
  simp [matrixImaginaryPart, hP.eq]
  apply Complex.ext <;> simp <;> ring

/-- **CEH spectral/resolvent identification.**  With the repository sign
convention `(A - (x+iη)I)⁻¹`, the kernel with positive Poisson weights is
exactly the matrix imaginary part of the resolvent. -/
theorem spectralImaginaryKernel_eq_matrixImaginaryPart_resolvent
    {N : ℕ} {A : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily A lam u)
    (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    spectralImaginaryKernel lam u x eta =
      matrixImaginaryPart
        ((A - ((x : ℂ) + (eta : ℂ) * Complex.I) •
          (1 : LocalETHMatrix N))⁻¹) := by
  rw [actualResolvent_eq_sum_spectralProjector hfamily x heta]
  rw [matrixImaginaryPart_sum]
  unfold spectralImaginaryKernel
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixImaginaryPart_smul_isHermitian _ _
    (spectralProjector_isHermitian u i)]
  congr 1
  simp only [cehSpectralWeight]
  rw [Complex.inv_im]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul,
    Complex.normSq]
  push_cast
  congr 1
  · ring
  · norm_num [Complex.normSq_apply]
    ring

end CEHNative.BlockBand.External.CEH
