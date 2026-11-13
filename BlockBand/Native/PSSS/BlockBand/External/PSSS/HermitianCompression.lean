module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.SpectralInduction
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Hermitian rank-one shifts and orthogonal compression

This module supplies the matrix-facing algebra used by the source-independent
PSSS lemmas.  It contains no APSSS tail estimate.  The perturbation and
compression are canonical matrices on the original finite coordinate space.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Matrix Topology

universe u

/-- The Hermitian positive rank-one perturbation `K + τ u uᴴ`. -/
def rankOneShift {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ) : HermitianMatrix ι :=
  ⟨K.1 + (τ : ℂ) • Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)),
    K.2.add (by
      have hv : (Matrix.vecMulVec (WithLp.ofLp u)
          (star (WithLp.ofLp u)) : Matrix ι ι ℂ).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_vecMulVec]
        simp
      exact hv.smul (by exact Complex.conj_ofReal τ))⟩

/-- The canonical orthogonal-compression matrix `P K Pᴴ`, with
`P = I - u uᴴ`.  For unit `u`, its restriction to `u⊥` is the
compression and its ambient-space representation carries one extra zero. -/
def orthogonalCompression {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) : HermitianMatrix ι :=
  let P : Matrix ι ι ℂ :=
    1 - Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))
  ⟨P * K.1 * Pᴴ, Matrix.isHermitian_mul_mul_conjTranspose P K.2⟩

@[simp] theorem rankOneShift_coe {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ) :
    (rankOneShift K u τ : Matrix ι ι ℂ) =
      K.1 + (τ : ℂ) • Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)) := rfl

@[simp] theorem orthogonalCompression_coe {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) :
    (orthogonalCompression K u : Matrix ι ι ℂ) =
      (1 - Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) * K.1 *
        (1 - Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)))ᴴ := rfl

/-- Nonnegative rank-one shifts increase every decreasingly sorted Hermitian
eigenvalue.  This is the matrix-level noncommuting Weyl monotonicity half of
rank-one interlacing. -/
theorem eigenvalues₀_rankOneShift_mono {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) {τ : ℝ} (hτ : 0 ≤ τ)
    (i : Fin (Fintype.card ι)) :
    K.2.eigenvalues₀ i ≤ (rankOneShift K u τ).2.eigenvalues₀ i := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.eigenvalue_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr K.2)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (rankOneShift K u τ).2)
    finrank_euclideanSpace
  intro x
  have hr : Matrix.toEuclideanLin
      (Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) =
        (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
          EuclideanSpace ℂ ι) := by
    have h := congrArg Matrix.toEuclideanLin
      (InnerProductSpace.symm_toEuclideanLin_rankOne u u)
    simpa using h.symm
  rw [show Matrix.toEuclideanLin (rankOneShift K u τ : Matrix ι ι ℂ) =
      Matrix.toEuclideanLin K.1 + (τ : ℂ) •
        Matrix.toEuclideanLin
          (Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) by
      change Matrix.toEuclideanLin
          (K.1 + (τ : ℂ) •
            Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) =
        _
      rw [map_add, map_smul]]
  rw [hr]
  rw [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, map_add]
  apply le_add_of_nonneg_right
  rw [inner_smul_left]
  change 0 ≤ RCLike.re ((starRingEnd ℂ) (τ : ℂ) *
    inner ℂ (InnerProductSpace.rankOne ℂ u u x) x)
  rw [InnerProductSpace.inner_left_rankOne_apply]
  rw [← inner_conj_symm x u]
  simp only [RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, neg_mul]
  have hre : RCLike.re (τ : ℂ) = τ := RCLike.ofReal_re τ
  have him : RCLike.im (τ : ℂ) = 0 := RCLike.ofReal_im τ
  rw [hre, him]
  simp only [zero_mul]
  ring_nf
  exact add_nonneg (mul_nonneg hτ (sq_nonneg _))
    (mul_nonneg hτ (sq_nonneg _))

end PSSSNative.BlockBand.PSSS
