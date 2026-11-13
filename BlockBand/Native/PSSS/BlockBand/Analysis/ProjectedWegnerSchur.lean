module

public import BlockBand.Native.PSSS.BlockBand.Analysis.SchurPositivity
public import BlockBand.Native.PSSS.BlockBand.Analysis.PositiveResolvent
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import BlockBand.Native.PSSS.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Native.PSSS.BlockBand.Analysis.PSSSPoissonAveraging

/-!
# Schur-complement bridge for projected Wegner averaging

This module implements the deterministic and conditioned one-block bridge in
the proof of the projected Wegner estimate.  The exposed block is the
upper-left block of a `Matrix.fromBlocks` decomposition.  Its resolvent block
is exactly the inverse of the lower-right Schur complement, and the Schur
complement inherits the full matrix's positive imaginary regulator.

For an exposed GUE block, the resulting arbitrary positive absorber is then
written in the noncommuting Cauchy–Poisson form.  Each real Cauchy background
is an ordinary deterministic Hermitian deformation, so the proved PSSS
Poisson estimate applies slice by slice.  No conditioning or independence
claim beyond the explicit `BlockGUE.Law` parameter is hidden here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

universe u

/-- The upper-left block of the nonsingular inverse of a block matrix is the
nonsingular inverse of the lower-right Schur complement.  Invertibility of the
exterior and of the full matrix are explicit; Schur invertibility follows from
Mathlib's block factorization. -/
theorem nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)] :
    ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl =
      (schurComplement₂₂ A B C D)⁻¹ := by
  change ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl =
    (A - B * ⅟D * C)⁻¹
  let _ : Invertible (A - B * ⅟D * C) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  rw [← Matrix.invOf_eq_nonsing_inv, ← Matrix.invOf_eq_nonsing_inv]
  exact invOf_fromBlocks_submatrix₁₁ A B C D

/-- Trace form of the exposed-block inverse identity, in the
negative-imaginary normalization. -/
theorem neg_im_trace_submatrix_nonsing_inv_fromBlocks_eq_schurComplement₂₂
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)] :
    -((((Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl).trace).im =
      -(((schurComplement₂₂ A B C D)⁻¹).trace).im := by
  rw [nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂
    A B C D]

/-- Deterministic projected-Wegner Schur bridge: the exposed resolvent trace
is the Schur-resolvent trace, while an `η I` lower bound on the full matrix
imaginary part passes to the Schur complement.  The two conclusions use the
same block convention and no commutativity assumption. -/
theorem exposedBlock_trace_eq_schur_and_regulator_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)]
    {η : ℝ} (hη : 0 ≤ η)
    (him :
      (matrixImaginaryPart (Matrix.fromBlocks A B C D) -
        (η : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef) :
    -((((Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl).trace).im =
        -(((schurComplement₂₂ A B C D)⁻¹).trace).im ∧
      (matrixImaginaryPart (schurComplement₂₂ A B C D) -
        (η : ℂ) • (1 : Matrix m m ℂ)).PosSemidef := by
  constructor
  · exact neg_im_trace_submatrix_nonsing_inv_fromBlocks_eq_schurComplement₂₂
      A B C D
  · exact schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
      A B C D hη him

end PSSSNative.BlockBand
