module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiAbsorbedCountFormula
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerFrozenSchurAverage
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.RegulatedSchurMeasurability

/-!
# Canonical Schur data for the PSSS first reduction

The regulated Schur complement of a block matrix splits into a Hermitian background plus `i`
times a positive semidefinite absorber, and the selected block of the regulated inverse is the
inverse of this Schur complement.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The Schur complement `A_r - B D_r⁻¹ C` of the regulated exterior block, where
`A_r = A - e + iη` and `D_r = frozenExteriorRegulated D e η`; Lean's inverse is total, and for
`η > 0` and Hermitian `D` the block `D_r` is invertible. -/
def canonicalFrozenSchur
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (e eta : ℝ) : Matrix m m ℂ :=
  let Ar := A - (e : ℂ) • (1 : Matrix m m ℂ) +
    Complex.I • (eta • (1 : Matrix m m ℂ))
  let Dr := frozenExteriorRegulated D e eta
  Ar - B * Dr⁻¹ * C

/-- The Hermitian part of `canonicalFrozenSchur`. -/
def canonicalFrozenBackground
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (e eta : ℝ) : Matrix m m ℂ :=
  matrixHermitianPart (canonicalFrozenSchur A B C D e eta)

/-- Canonical positive absorber, with the scalar regulator removed. -/
def canonicalFrozenAbsorber
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (e eta : ℝ) : Matrix m m ℂ :=
  matrixImaginaryPart (canonicalFrozenSchur A B C D e eta) -
    (eta : ℂ) • (1 : Matrix m m ℂ)

/-- The canonical background is Hermitian for all parameters. -/
theorem canonicalFrozenBackground_isHermitian
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (e eta : ℝ) :
    (canonicalFrozenBackground A B C D e eta).IsHermitian :=
  matrixHermitianPart_isHermitian _

/-- Exact algebraic decomposition of the canonical Schur complement. -/
theorem canonicalFrozenSchur_eq_background_add_I_absorber
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (e eta : ℝ) :
    canonicalFrozenSchur A B C D e eta =
      canonicalFrozenBackground A B C D e eta +
        Complex.I • (canonicalFrozenAbsorber A B C D e eta +
          (eta : ℂ) • (1 : Matrix m m ℂ)) := by
  rw [show canonicalFrozenAbsorber A B C D e eta +
      (eta : ℂ) • (1 : Matrix m m ℂ) =
      matrixImaginaryPart (canonicalFrozenSchur A B C D e eta) by
    simp [canonicalFrozenAbsorber]]
  simpa [canonicalFrozenBackground] using
    (matrix_eq_hermitianPart_add_I_imaginaryPart
      (canonicalFrozenSchur A B C D e eta))

/-- For a Hermitian full matrix and `η > 0`, the canonical absorber is positive
semidefinite. -/
theorem canonicalFrozenAbsorber_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hH : (Matrix.fromBlocks A B C D).IsHermitian)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (canonicalFrozenAbsorber A B C D e eta).PosSemidef := by
  let Ar : Matrix m m ℂ :=
    A - (e : ℂ) • (1 : Matrix m m ℂ) +
      Complex.I • (eta • (1 : Matrix m m ℂ))
  let Dr : Matrix n n ℂ := frozenExteriorRegulated D e eta
  have hbase : (Matrix.fromBlocks A B C D -
      (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal e)))
  have him : (matrixImaginaryPart (Matrix.fromBlocks Ar B C Dr) -
      (eta : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef := by
    have hshape : Matrix.fromBlocks Ar B C Dr =
        (Matrix.fromBlocks A B C D -
          (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)) +
          Complex.I • ((eta : ℂ) •
            (1 : Matrix (Sum m n) (Sum m n) ℂ)) := by
      ext (i | i) (j | j) <;>
        simp [Ar, Dr, frozenExteriorRegulated, Matrix.fromBlocks,
          Matrix.one_apply]
    rw [hshape, matrixImaginaryPart_add_I_smul _ _ hbase
      (Matrix.isHermitian_one.smul
        (isSelfAdjoint_iff.mpr (Complex.conj_ofReal eta)))]
    simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Sum m n) (Sum m n) ℂ).PosSemidef)
  have hDu : IsUnit Dr := by
    apply isUnit_frozenExteriorRegulated D
    exact (Matrix.isHermitian_fromBlocks_iff.mp hH).2.2.2
    exact heta
  let _ : Invertible Dr := hDu.invertible
  have hs := schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
    Ar B C Dr heta.le him
  simpa [canonicalFrozenAbsorber, canonicalFrozenSchur, Ar, Dr,
    schurComplement₂₂, Matrix.invOf_eq_nonsing_inv] using hs

/-- Schur separation with explicit data: for a Hermitian full matrix, Hermitian `V` and
`η > 0`, the selected block of the regulated inverse is
`(V + background + i(absorber + η))⁻¹`. -/
theorem frozenSelectedInverse_eq_canonicalSchur
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hH : (Matrix.fromBlocks A B C D).IsHermitian)
    (V : Matrix m m ℂ) (hV : V.IsHermitian) (e : ℝ)
    {eta : ℝ} (heta : 0 < eta) :
    ((frozenFullRegulated A B C D V e eta)⁻¹).submatrix Sum.inl Sum.inl =
      (V + canonicalFrozenBackground A B C D e eta +
        Complex.I • (canonicalFrozenAbsorber A B C D e eta +
          (eta : ℂ) • (1 : Matrix m m ℂ)))⁻¹ := by
  let Ar : Matrix m m ℂ :=
    A - (e : ℂ) • (1 : Matrix m m ℂ) +
      Complex.I • (eta • (1 : Matrix m m ℂ))
  let Dr : Matrix n n ℂ := frozenExteriorRegulated D e eta
  have hDu : IsUnit Dr := isUnit_frozenExteriorRegulated D
    (Matrix.isHermitian_fromBlocks_iff.mp hH).2.2.2 e heta
  let _ : Invertible Dr := hDu.invertible
  have hVU := isUnit_frozenFullRegulated A B C D hH V hV e heta
  let _ : Invertible (frozenFullRegulated A B C D V e eta) := hVU.invertible
  have hshape : frozenFullRegulated A B C D V e eta =
      Matrix.fromBlocks (Ar + V) B C Dr := by
    rw [frozenFullRegulated_eq_fromBlocks]
    congr 1
    dsimp [Ar]
    noncomm_ring
  let _ : Invertible (Matrix.fromBlocks (Ar + V) B C Dr) := by
    rw [← hshape]
    infer_instance
  rw [hshape, nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂]
  congr 1
  have hschur :
      schurComplement₂₂ (Ar + V) B C Dr =
        V + canonicalFrozenSchur A B C D e eta := by
    simp only [canonicalFrozenSchur, Ar, Dr, schurComplement₂₂,
      Matrix.invOf_eq_nonsing_inv]
    noncomm_ring
  rw [hschur, canonicalFrozenSchur_eq_background_add_I_absorber]
  abel

end PSSSNative.BlockBand.PSSS
