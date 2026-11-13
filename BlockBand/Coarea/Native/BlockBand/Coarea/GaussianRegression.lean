module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairCoordinates
public import Mathlib.Analysis.Complex.Basic

/-!
# Gaussian regression in canonical eigenpair coordinates

This file proves the exact Hilbert–Schmidt square separation used in the Gaussian
regression step of the coarea theorem.  The selected eigenvector is put in
the first coordinate.  The scalar, off-diagonal, and complementary blocks are
then orthogonal for the Hilbert–Schmidt inner product, with the off-diagonal
column occurring twice in a Hermitian matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped BigOperators

/-- Squared Hilbert–Schmidt norm, written entrywise to avoid choosing one of
the competing matrix norm instances. -/
def hilbertSchmidtNormSq
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- Squared Euclidean norm of a finite complex column. -/
def complexColumnNormSq {n : Type*} [Fintype n] (q : n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (q i)

/-- The Hilbert–Schmidt square of a block matrix is the sum of the four
block squares. -/
theorem hilbertSchmidtNormSq_fromBlocks
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m p ℂ) (B : Matrix m q ℂ)
    (C : Matrix n p ℂ) (D : Matrix n q ℂ) :
    hilbertSchmidtNormSq (Matrix.fromBlocks A B C D) =
      hilbertSchmidtNormSq A + hilbertSchmidtNormSq B +
        hilbertSchmidtNormSq C + hilbertSchmidtNormSq D := by
  simp only [hilbertSchmidtNormSq, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

/-- Canonical block form of the Gaussian regression identity.

Normalization: the selected direction is the first `Unit` coordinate; `q`
is the component of `Fv` perpendicular to that direction, and `Fv` below is
the compression of `F` to the orthogonal complement.  The equality is exact
in every finite dimension and has no asymptotic or probabilistic hypothesis. -/
theorem canonicalGaussianRegression
    {n : Type*} [Fintype n] [DecidableEq n]
    (E f : ℝ) (q : n → ℂ) (B Fv : Matrix n n ℂ) :
    hilbertSchmidtNormSq
        (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B -
          Matrix.fromBlocks ((f : ℂ) • (1 : Matrix Unit Unit ℂ))
            (eigenpairTangentColumn q)ᴴ (eigenpairTangentColumn q) Fv) =
      (E - f) ^ 2 + 2 * complexColumnNormSq q +
        hilbertSchmidtNormSq (B - Fv) := by
  have hblocks :
      Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B -
          Matrix.fromBlocks ((f : ℂ) • (1 : Matrix Unit Unit ℂ))
            (eigenpairTangentColumn q)ᴴ (eigenpairTangentColumn q) Fv =
        Matrix.fromBlocks
          ((E : ℂ) • (1 : Matrix Unit Unit ℂ) -
            (f : ℂ) • (1 : Matrix Unit Unit ℂ))
          (-(eigenpairTangentColumn q)ᴴ) (-(eigenpairTangentColumn q))
          (B - Fv) := by
    ext i j
    cases i <;> cases j <;> simp
  rw [hblocks]
  rw [hilbertSchmidtNormSq_fromBlocks]
  simp [hilbertSchmidtNormSq, complexColumnNormSq,
    eigenpairTangentColumn, Complex.normSq_neg, Complex.normSq_conj]
  rw [show (E : ℂ) - (f : ℂ) = ((E - f : ℝ) : ℂ) by norm_num,
    Complex.normSq_ofReal]
  ring

end CoareaNative.BlockBand
