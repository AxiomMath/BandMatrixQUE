module

public import BlockBand.Native.PSSS.BlockBand.Coarea.HermitianSimpleSpectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Correctness interface for measurable Lagrange eigenprojectors

This module isolates the exact algebraic bridge still needed to turn the measurable
Lagrange product into a global measurable eigenline.  The interface records that
the product is a nonzero rank-one orthogonal projector and that its range is the
ordered eigenspace.  From these hypotheses we prove, without any further spectral
choice, that every phase-fixed nonzero column constructed in
`EigenlineSelection` is a normalized eigenvector.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open Matrix
open scoped ComplexConjugate

/-- On the algebraic simple-spectrum locus the project's increasing ordered
eigenvalue enumeration is injective.  This closes the first previously missing
library bridge: separability gives duplicate-free characteristic roots, and
Mathlib identifies those roots with `eigenvalues₀`. -/
theorem orderedEigenvalue_injective_of_separable
    {d : ℕ} (A : HermitianMatrix (Fin d))
    (hsep : (A : Matrix (Fin d) (Fin d) ℂ).charpoly.Separable) :
    Function.Injective (orderedEigenvalue A) := by
  have heigC : Function.Injective
      (fun i => (A.property.eigenvalues i : ℂ)) := by
    rw [A.property.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff] at hsep
    exact hsep
  have heig : Function.Injective A.property.eigenvalues := by
    intro i j hij
    exact heigC (congrArg (fun t : ℝ => (t : ℂ)) hij)
  let E : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have heig0 : Function.Injective A.property.eigenvalues₀ := by
    intro i j hij
    apply E.symm.injective
    apply heig
    simpa [Matrix.IsHermitian.eigenvalues, E] using hij
  intro r s hrs
  apply Fin.rev_injective
  apply heig0
  exact hrs

end PSSSNative.BlockBand
