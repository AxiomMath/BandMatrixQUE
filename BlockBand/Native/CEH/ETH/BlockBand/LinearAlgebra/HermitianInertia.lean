module

public import BlockBand.Native.CEH.ETH.BlockBand.LinearAlgebra.SchurCongruence
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Negative spectral count for finite Hermitian matrices

Mathlib supplies ordered eigenvalues for finite Hermitian matrices, but currently has no
Sylvester-law API for invariance of inertia under arbitrary invertible congruence.  This
module fixes the negative-count normalization used by eigenpair coarea and proves the
parts available from the spectral and positivity APIs: proof independence, the dimension
bound, characteristic-polynomial transport, the zero-index characterization, and
zero-index invariance under invertible congruence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- Number of strictly negative eigenvalues of a finite Hermitian matrix, counted with
multiplicity.

Source: the rank-sector convention following the Schur graph identity in the RBM
coarea argument.  Eigenvalues equal to zero are not counted.  The count is finite and
contains no probabilistic parameter, uniformity, or limiting operation. -/
def negativeEigenvalueCount
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i < 0).card

/-- The negative eigenvalue count is independent of the proof of Hermiticity used to
construct the ordered eigenvalue family. -/
theorem negativeEigenvalueCount_proof_irrel
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA hA' : A.IsHermitian) :
    negativeEigenvalueCount hA = negativeEigenvalueCount hA' := by
  congr

/-- A negative eigenvalue count never exceeds the ambient finite dimension. -/
theorem negativeEigenvalueCount_le_card
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    negativeEigenvalueCount hA ≤ Fintype.card n := by
  unfold negativeEigenvalueCount
  simpa using Finset.card_filter_le (Finset.univ : Finset n) (fun i => hA.eigenvalues i < 0)

/-- Hermitian matrices with the same characteristic polynomial have the same negative
spectral count.  This is the reusable transport layer for unitary similarity; arbitrary
congruence requires Sylvester's law rather than characteristic-polynomial invariance. -/
theorem negativeEigenvalueCount_eq_of_charpoly_eq
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchar : A.charpoly = B.charpoly) :
    negativeEigenvalueCount hA = negativeEigenvalueCount hB := by
  have heig : hA.eigenvalues = hB.eigenvalues :=
    (hA.eigenvalues_eq_eigenvalues_iff hB).2 hchar
  unfold negativeEigenvalueCount
  rw [heig]

/-- The negative count vanishes exactly for positive-semidefinite Hermitian matrices.
This identifies the zero sector of inertia using Mathlib's spectral positivity theorem. -/
theorem negativeEigenvalueCount_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    negativeEigenvalueCount hA = 0 ↔ A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  unfold negativeEigenvalueCount
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i
    exact le_of_not_gt (h (x := i))
  · intro h i
    exact not_lt_of_ge (h i)

/-- The zero-negative-index sector is invariant under congruence by an invertible
matrix.  This is the zero-sector instance of Sylvester invariance and follows from
Mathlib's congruence invariance of positive semidefiniteness. -/
theorem negativeEigenvalueCount_congruence_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} (hA : A.IsHermitian) (hU : IsUnit U) :
    let hConj : (Uᴴ * A * U).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul U hA
    negativeEigenvalueCount hConj = 0 ↔ negativeEigenvalueCount hA = 0 := by
  dsimp only
  rw [negativeEigenvalueCount_eq_zero_iff, negativeEigenvalueCount_eq_zero_iff]
  simpa only [star_eq_conjTranspose] using hU.posSemidef_star_left_conjugate_iff (x := A)

/-- With a positive-definite exterior block, the full Hermitian block matrix has no
negative eigenvalues exactly when its Schur complement has none.

Source: zero-rank sector of the inertia relation after `hermitianSchur_congruence`.
The exterior block is assumed positive definite, as in the positive-resolvent sector;
there are no asymptotic parameters or limit-order claims. -/
theorem negativeEigenvalueCount_fromBlocks_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D] (hD : D.PosDef)
    (hA : A.IsHermitian) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      (Matrix.isHermitian_fromBlocks_iff.mpr ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B,
        hD.isHermitian⟩)
    let hSchur : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hD.isHermitian.inv)
    negativeEigenvalueCount hFull = 0 ↔ negativeEigenvalueCount hSchur = 0 := by
  dsimp only
  rw [negativeEigenvalueCount_eq_zero_iff, negativeEigenvalueCount_eq_zero_iff]
  exact Matrix.PosDef.fromBlocks₂₂ A B hD

end CEHNative.BlockBand
