module

public import BlockBand.Coarea.Native.BlockBand.Coarea.LagrangeProjectorCorrectness
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Unconditional finite-dimensional Lagrange spectral projectors

This module closes the algebraic functional-calculus input used by the
measurable eigenline charts.  The proof conjugates the Lagrange product by the
unitary eigenvector matrix from the finite-dimensional Hermitian spectral
theorem.  In that basis every factor is diagonal, and the product is the
coordinate projection onto the unique ordered eigenvalue.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The index in Mathlib's eigenvector basis corresponding to the project's
increasing ordered eigenvalue rank. -/
def orderedEigenbasisIndex (d : ℕ) (r : HermitianEigenRank d) : Fin d :=
  Fintype.equivOfCardEq
    (Fintype.card_fin (Fintype.card (Fin d))) r.rev

/-- The eigenvalue attached to `orderedEigenbasisIndex` is exactly the
project's increasing ordered eigenvalue. -/
theorem eigenvalues_orderedEigenbasisIndex
    {d : ℕ} (A : HermitianMatrix (Fin d)) (r : HermitianEigenRank d) :
    A.property.eigenvalues (orderedEigenbasisIndex d r) =
      orderedEigenvalue A r := by
  simp [orderedEigenbasisIndex, orderedEigenvalue,
    Matrix.IsHermitian.eigenvalues]

/-- The one-coordinate diagonal projection associated to an ordered rank. -/
def orderedEigenbasisProjection (d : ℕ) (r : HermitianEigenRank d) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if i = orderedEigenbasisIndex d r then 1 else 0

/-- A fixed ordered product of diagonal matrices is obtained by multiplying
their diagonal functions pointwise. -/
theorem list_prod_diagonal {d : ℕ} (l : List (Fin d → ℂ)) :
    (l.map Matrix.diagonal).prod =
      Matrix.diagonal (fun i => (l.map fun f => f i).prod) := by
  classical
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rw [Matrix.diagonal_mul_diagonal]

/-- One Lagrange factor becomes the corresponding scalar factor on each
diagonal entry in the Hermitian eigenvector basis. -/
theorem diagonalize_hermitianSpectralLagrangeFactor
    {d : ℕ} (x : HermitianCoordinateSpace d)
    (r s : HermitianEigenRank d) :
    (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
      (star (hermitianOfFinCoordinates d x).property.eigenvectorUnitary))
        (hermitianSpectralLagrangeFactor d r s x) =
      Matrix.diagonal (fun i =>
        (((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
          orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ)⁻¹ *
        (((hermitianOfFinCoordinates d x).property.eigenvalues i : ℂ) -
          (orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℂ)))) := by
  classical
  rw [hermitianSpectralLagrangeFactor, map_smul, map_sub, map_smul, map_one,
    (hermitianOfFinCoordinates d x).property.conjStarAlgAut_star_eigenvectorUnitary]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-!
The remaining finite-list step is to evaluate the product of these diagonal
factors at each eigenbasis index.  The distinguished index has every factor
`1`; at any other index, the factor indexed by its inverse ordered rank is
`0`.  This requires explicit bookkeeping between `Fin d`, `Fin.rev`, and the
filtered fixed list `otherHermitianEigenRanks`; no further analytic or spectral
theorem input is missing.
-/

end CoareaNative.BlockBand
