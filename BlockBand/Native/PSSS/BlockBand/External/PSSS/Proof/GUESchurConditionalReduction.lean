module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEArbitraryVectorDisintegration
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Exact Schur reduction for the canonical GUE first-row split

This module records the deterministic block inverse identity used after rotating
a fixed unit vector to the zeroth coordinate.  It deliberately separates the
exact Schur algebra from the remaining probabilistic realification step: the
latter must identify the concrete first-row marginal with one standard real
and `N-1` standard circular-complex Gaussians before `quadraticRatio_tail` can
be applied.  A second required input, not present in the current PSSS modules,
is almost-everywhere nonvanishing of the deterministically shifted compression
determinant.  Consequently this file proves no probability estimate and
introduces no substitute hypothesis for either missing measure theorem.

The empty compression (`N = 1`) is included in every block identity below:
its sums are empty and its determinant is one.  Dimension zero is
excluded, since it has no unit vector.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- A scalar viewed as a one-by-one matrix. -/
def schurScalarMatrix (a : ℂ) : Matrix Unit Unit ℂ := fun _ _ => a

/-- A complex column and its adjoint row. -/
def schurColumn {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) Unit ℂ :=
  fun i _ => b i

def schurRow {n : ℕ} (b : Fin n → ℂ) : Matrix Unit (Fin n) ℂ :=
  fun _ j => star (b j)

/-- Hermitian block matrix with distinguished zeroth coordinate. -/
def schurBlockMatrix {n : ℕ} (a : ℂ) (b : Fin n → ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (schurScalarMatrix a) (schurRow b) (schurColumn b) D

/-- The scalar Schur denominator `a - bᴴ D⁻¹ b`. -/
def schurDenominator {n : ℕ} (a : ℂ) (b : Fin n → ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  a - dotProduct (star b) (D⁻¹ *ᵥ b)

/-- The canonical distinguished coordinate in the block index. -/
def schurFirstCoordinate {n : ℕ} : Unit ⊕ Fin n → ℂ
  | .inl _ => 1
  | .inr _ => 0

/-- Exact first column of the inverse in Schur coordinates.  The assumptions
are precisely the two algebraic nonvanishing conditions; no probabilistic
null-set claim is hidden here. -/
theorem schurBlockMatrix_inv_mulVec_firstCoordinate {n : ℕ}
    (a : ℂ) (b : Fin n → ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.det ≠ 0) (hs : schurDenominator a b D ≠ 0) :
    (schurBlockMatrix a b D)⁻¹ *ᵥ schurFirstCoordinate =
      fun i => match i with
      | .inl _ => (schurDenominator a b D)⁻¹
      | .inr j => -((D⁻¹ *ᵥ b) j * (schurDenominator a b D)⁻¹) := by
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  let _ : Invertible D := Matrix.invertibleOfIsUnitDet D hDu
  let S : Matrix Unit Unit ℂ := schurScalarMatrix (schurDenominator a b D)
  have hSdet : S.det ≠ 0 := by
    simpa [S, schurScalarMatrix] using hs
  let _ : Invertible S :=
    { invOf := schurScalarMatrix (schurDenominator a b D)⁻¹
      invOf_mul_self := by
        ext i j
        cases i
        cases j
        rw [Matrix.mul_apply]
        simp [S, schurScalarMatrix, hs]
      mul_invOf_self := by
        ext i j
        cases i
        cases j
        rw [Matrix.mul_apply]
        simp [S, schurScalarMatrix, hs] }
  have hschur : schurScalarMatrix a - schurRow b * ⅟D * schurColumn b = S := by
    ext i j
    cases i
    cases j
    change a - ((schurRow b * D⁻¹ * schurColumn b) () ()) =
      a - dotProduct (star b) (D⁻¹ *ᵥ b)
    congr 1
    change (schurRow b () ᵥ* D⁻¹) ⬝ᵥ b =
      (star b) ⬝ᵥ (D⁻¹ *ᵥ b)
    rw [Matrix.dotProduct_mulVec]
    rfl
  let _ : Invertible
      (schurScalarMatrix a - schurRow b * ⅟D * schurColumn b) :=
    Invertible.copy (inferInstance : Invertible S) _ hschur
  let _ : Invertible (schurBlockMatrix a b D) :=
    Matrix.fromBlocks₂₂Invertible _ _ _ _
  rw [← Matrix.invOf_eq_nonsing_inv]
  unfold schurBlockMatrix
  rw [Matrix.invOf_fromBlocks₂₂_eq]
  change (Matrix.fromBlocks
      (schurScalarMatrix (schurDenominator a b D)⁻¹)
      (-((schurScalarMatrix (schurDenominator a b D)⁻¹) *
        schurRow b * D⁻¹))
      (-(D⁻¹ * schurColumn b *
        schurScalarMatrix (schurDenominator a b D)⁻¹))
      (D⁻¹ + D⁻¹ * schurColumn b *
        schurScalarMatrix (schurDenominator a b D)⁻¹ *
        schurRow b * D⁻¹) *ᵥ schurFirstCoordinate) = _
  rw [Matrix.fromBlocks_mulVec]
  ext i
  cases i with
  | inl i =>
      cases i
      simp [schurFirstCoordinate, schurScalarMatrix, Matrix.mulVec,
        dotProduct, Function.comp_apply]
  | inr i =>
      simp [schurFirstCoordinate, schurScalarMatrix,
        schurColumn, Matrix.mulVec, dotProduct, Function.comp_apply,
        Matrix.mul_apply]

/-- Squared Euclidean norm form of the Schur inverse-vector identity.  It
exhibits exactly the numerator `1 + ‖D⁻¹b‖²` and denominator
`|a - bᴴD⁻¹b|²` used in the APSSS conditional split. -/
theorem norm_sq_schurBlockMatrix_inv_mulVec_firstCoordinate {n : ℕ}
    (a : ℂ) (b : Fin n → ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.det ≠ 0) (hs : schurDenominator a b D ≠ 0) :
    ‖(WithLp.toLp 2 ((schurBlockMatrix a b D)⁻¹ *ᵥ schurFirstCoordinate) :
        EuclideanSpace ℂ (Unit ⊕ Fin n))‖ ^ 2 =
      ‖(schurDenominator a b D)⁻¹‖ ^ 2 *
        (1 + ∑ j : Fin n, ‖(D⁻¹ *ᵥ b) j‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [schurBlockMatrix_inv_mulVec_firstCoordinate a b D hD hs]
  rw [Fintype.sum_sum_type]
  simp only [norm_neg, norm_mul]
  simp
  rw [← inv_pow]
  simp_rw [mul_pow]
  rw [← Finset.sum_mul]
  ring

/-- Deterministic two-event split underlying the APSSS conditioning argument.
The factor `2` is explicit: a large inverse vector forces either the scalar
Gaussian denominator event or the quadratic-ratio event. -/
theorem schur_ratio_two_event_split {t s q : ℝ}
    (hq : 0 ≤ q)
    (h : (t * s) ^ 2 ≤ 1 + q ^ 2) :
    t / 2 * s ≤ 1 ∨ t / 2 * s ≤ q := by
  by_contra hn
  push Not at hn
  rcases hn with ⟨h1, hq'⟩
  by_cases hsmall : q ^ 2 ≤ 1 / 3
  · have hts : 2 < t * s := by nlinarith
    nlinarith [sq_nonneg (t * s - 2)]
  · have hts : 2 * q < t * s := by nlinarith
    nlinarith [sq_nonneg (t * s - 2 * q), sq_nonneg q]

/-- The canonical equivalence splitting `Fin (n+1)` into its zeroth coordinate
and the remaining `n` coordinates. -/
def zerothSplitEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) (Equiv.refl (Fin n))).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n)))

/-- Simultaneous reindexing of a matrix into zeroth-coordinate block form. -/
def zerothBlockReindex {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ :=
  Matrix.reindex (zerothSplitEquiv n).symm (zerothSplitEquiv n).symm H

/-- Distinguished diagonal entry of a matrix in zeroth-coordinate block form. -/
def zerothBlockScalar {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℂ :=
  zerothBlockReindex H (Sum.inl ()) (Sum.inl ())

/-- Lower part of the distinguished column. -/
def zerothBlockColumn {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Fin n → ℂ := fun i => zerothBlockReindex H (Sum.inr i) (Sum.inl ())

/-- Principal compression complementary to the zeroth coordinate. -/
def zerothBlockCompression {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => zerothBlockReindex H (Sum.inr i) (Sum.inr j)

/-- A Hermitian matrix is exactly its scalar/column/compression Schur block
reconstruction after the canonical zeroth-coordinate reindexing. -/
theorem zerothBlockReindex_eq_schurBlock {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian) :
    zerothBlockReindex H =
      schurBlockMatrix (zerothBlockScalar H) (zerothBlockColumn H)
        (zerothBlockCompression H) := by
  have hR : (zerothBlockReindex H).IsHermitian := by
    exact hH.submatrix (zerothSplitEquiv n)
  ext i j
  cases i with
  | inl i =>
      cases i
      cases j with
      | inl j => cases j; rfl
      | inr j =>
          have h := congrArg (fun M : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ =>
            M (Sum.inr j) (Sum.inl ())) hR
          have hs := congrArg star h
          simpa [zerothBlockScalar, zerothBlockColumn,
            zerothBlockCompression, schurBlockMatrix, schurRow] using hs
  | inr i =>
      cases j with
      | inl j => cases j; rfl
      | inr j => rfl

/-- Exact squared-norm Schur formula for a finite Hermitian matrix in
canonical zeroth-coordinate block form. -/
theorem norm_sq_zerothBlockReindex_inv_mulVec_firstCoordinate {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian)
    (hD : (zerothBlockCompression H).det ≠ 0)
    (hs : schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
      (zerothBlockCompression H) ≠ 0) :
    ‖(WithLp.toLp 2 ((zerothBlockReindex H)⁻¹ *ᵥ schurFirstCoordinate) :
        EuclideanSpace ℂ (Unit ⊕ Fin n))‖ ^ 2 =
      ‖(schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
        (zerothBlockCompression H))⁻¹‖ ^ 2 *
        (1 + ∑ j : Fin n,
          ‖((zerothBlockCompression H)⁻¹ *ᵥ zerothBlockColumn H) j‖ ^ 2) := by
  rw [zerothBlockReindex_eq_schurBlock H hH]
  exact norm_sq_schurBlockMatrix_inv_mulVec_firstCoordinate _ _ _ hD hs

end PSSSNative.BlockBand.PSSS
