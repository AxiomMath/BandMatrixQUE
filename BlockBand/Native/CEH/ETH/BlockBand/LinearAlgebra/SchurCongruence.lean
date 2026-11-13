module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Schur-complement block diagonalization

This file isolates the deterministic matrix identity underlying the rank-sector step in
eigenpair coarea.  It is deliberately stated for arbitrary finite index types and a
commutative coefficient ring.  In the Hermitian specialization, the two elimination
factors are conjugate transposes, so the identity is precisely the congruence reduction
to which Sylvester's law of inertia applies.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix

variable {m n R : Type*}

/-- Exact two-sided elimination of a block matrix around an invertible exterior block.

Source: deterministic linear-algebra step following the Schur graph identity in the
RBM eigenpair-coarea argument.  Normalization: the `m` block is the retained sector,
the `n` block is the exterior sector, and the Schur complement is
`A - B * ⅟D * C`.  Quantifiers range over arbitrary finite index types and a
commutative ring; there are no probabilistic uniformities or limiting operations. -/
theorem schurComplement₂₂_elimination
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R]
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible D] :
    fromBlocks 1 (-(B * ⅟D)) 0 1 * fromBlocks A B C D *
        fromBlocks 1 0 (-(⅟D * C)) 1 =
      fromBlocks (A - B * ⅟D * C) 0 0 D := by
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc, sub_eq_add_neg]

/-- For a Hermitian exterior block, the lower unitriangular elimination factor has
conjugate transpose equal to the upper elimination factor.

Source and normalization are as in `schurComplement₂₂_elimination`, with the lower-left
block specialized to `Bᴴ`.  This is the adjointness input that turns two-sided Gaussian
elimination into Hermitian congruence.  There are no asymptotic parameters. -/
theorem schurLower_conjTranspose
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] [StarRing R]
    (B : Matrix m n R) (D : Matrix n n R) [Invertible D]
    (hD : D.IsHermitian) :
    (fromBlocks 1 0 (-(⅟D * Bᴴ)) 1 : Matrix (m ⊕ n) (m ⊕ n) R)ᴴ =
      fromBlocks 1 (-(B * ⅟D)) 0 1 := by
  have hi : (⅟D)ᴴ = ⅟D := by
    rw [Matrix.invOf_eq_nonsing_inv D]
    exact hD.inv.eq
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg,
    conjTranspose_mul, conjTranspose_conjTranspose, hi]

/-- A Hermitian block matrix with invertible exterior block is congruent to the block
diagonal matrix consisting of its Schur complement and the exterior block.

Source: deterministic rank-sector reduction after the Schur graph identity in the RBM
eigenpair-coarea argument.  Normalization: retained coordinates precede exterior
coordinates, the off-diagonal blocks are `B` and `Bᴴ`, and the congruence factor is
lower unitriangular.  This exact equality is the reduction needed to apply Sylvester's
law of inertia once an inertia API is available.  It is finite-dimensional and contains
no uniformity or limit-order assertion. -/
theorem hermitianSchur_congruence
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] [StarRing R]
    (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) [Invertible D] (hD : D.IsHermitian) :
    let U : Matrix (m ⊕ n) (m ⊕ n) R :=
      fromBlocks 1 0 (-(⅟D * Bᴴ)) 1
    Uᴴ * fromBlocks A B Bᴴ D * U =
      fromBlocks (A - B * ⅟D * Bᴴ) 0 0 D := by
  dsimp only
  rw [schurLower_conjTranspose B D hD]
  exact schurComplement₂₂_elimination A B Bᴴ D

end CEHNative.BlockBand
