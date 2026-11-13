module

public import BlockBand.Model.Construction.OrderedSpectrum
public import Mathlib.FieldTheory.Separable

/-!
# Separability and simplicity of the increasing spectrum

If the characteristic polynomial of a Hermitian matrix is separable, its increasing eigenvalue
enumeration is injective; the Hermitian matrices with distinct increasing eigenvalues form a Borel
set.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open BlockBand.Foundations.Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Separability of the characteristic polynomial implies injectivity of the increasing
eigenvalue enumeration. -/
theorem orderedEigenvalue_injective_of_separable (A : HermitianMatrix ι)
    (hsep : A.val.charpoly.Separable) : Function.Injective (orderedEigenvalue A) := by
  have heigC : Function.Injective (fun x => (A.property.eigenvalues x : ℂ)) := by
    rw [A.property.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff] at hsep
    exact hsep
  have heig : Function.Injective A.property.eigenvalues := by
    intro x y hxy
    exact heigC (congrArg (fun t : ℝ => (t : ℂ)) hxy)
  intro i j hij
  apply increasingIndex.injective
  apply heig
  simpa only [eigenvalue_increasingIndex, orderedEigenvalue] using hij

/-- Distinct increasing values define a Borel subset of Hermitian matrices. -/
theorem measurableSet_injective_orderedEigenvalue :
    MeasurableSet {A : HermitianMatrix ι | Function.Injective (orderedEigenvalue A)} := by
  have hs : {A : HermitianMatrix ι | Function.Injective (orderedEigenvalue A)} =
      ⋂ i : Fin (Fintype.card ι), ⋂ j : Fin (Fintype.card ι), ⋂ (_ : i ≠ j),
        {A | orderedEigenvalue A i ≠ orderedEigenvalue A j} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j hij heq
      exact hij (h heq)
    · intro h i j heq
      by_contra hij
      exact h i j hij heq
  rw [hs]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_orderedEigenvalue i)
        (measurable_orderedEigenvalue j)).compl

end BlockBand.Model.Construction
