module

public import BlockBand.Native.PSSS.Shared.Upstream.SpectralOrdered

/-!
# Increasing Hermitian eigenvalues and counts

`orderedEigenvalue A` enumerates the eigenvalues of a Hermitian matrix in increasing order, and
`eigenCount A s` is the multiplicity-counted number of them in a set `s`. An entrywise
`ε`-perturbation moves each ordered eigenvalue by at most `card ι * ε`.
-/

set_option autoImplicit false

@[expose] public section

namespace PSSSNative.BlockBand

open scoped ComplexOrder Matrix.Norms.L2Operator
open PSSSNative.Shared.Upstream.SpectralOrdered

/-- Finite complex Hermitian matrices, with the subtype
topology and measurable space inherited from the raw matrix type.
-/
abbrev HermitianMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {A : Matrix ι ι ℂ // A.IsHermitian}

section OrderedEigenvalues

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Increasing ordered eigenvalue: the decreasing Mathlib enumeration reindexed
by `Fin.rev`. Index `i` represents the `(i.val + 1)`-st eigenvalue. -/
noncomputable def orderedEigenvalue (A : HermitianMatrix ι)
    (i : Fin (Fintype.card ι)) : ℝ :=
  A.property.eigenvalues₀ i.rev

/-- The enumeration is increasing. -/
theorem orderedEigenvalue_mono (A : HermitianMatrix ι) :
    Monotone (orderedEigenvalue A) := by
  intro i j hij
  exact A.property.eigenvalues₀_antitone ((Fin.rev_le_rev).2 hij)

/-- An entrywise `ε` perturbation changes every increasing ordered eigenvalue
by at most `card ι * ε`; no positivity of `ε` is hidden. -/
theorem orderedEigenvalue_entrywisePerturbation
    (A B : HermitianMatrix ι) {ε : ℝ}
    (hentry : ∀ i j, ‖(A : Matrix ι ι ℂ) i j - (B : Matrix ι ι ℂ) i j‖ ≤ ε)
    (k : Fin (Fintype.card ι)) :
    |orderedEigenvalue A k - orderedEigenvalue B k| ≤ (Fintype.card ι : ℝ) * ε :=
  sortedEigenvalueEntrywisePerturbation A.property B.property hentry k.rev

end OrderedEigenvalues

section Counts

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplicity-counted number of increasing ordered eigenvalues in a set. -/
noncomputable def eigenCount (A : HermitianMatrix ι) (s : Set ℝ) : ℕ := by
  classical
  exact Finset.card (Finset.univ.filter fun i => orderedEigenvalue A i ∈ s)

/-- The defining finite-filter formula for eigenvalue counts. -/
theorem eigenCount_def (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s = (Finset.univ.filter fun i => orderedEigenvalue A i ∈ s).card := by
  classical
  rfl

/-- Eigenvalue counts are monotone in the counted set. -/
theorem eigenCount_mono (A : HermitianMatrix ι) {s t : Set ℝ} (hst : s ⊆ t) :
    eigenCount A s ≤ eigenCount A t := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hst hi

/-- A singleton has zero multiplicity count exactly when no ordered
eigenvalue equals its point. -/
theorem eigenCount_singleton_eq_zero_iff (A : HermitianMatrix ι) (e : ℝ) :
    eigenCount A {e} = 0 ↔ ∀ i, orderedEigenvalue A i ≠ e := by
  classical
  simp [eigenCount]

end Counts

end PSSSNative.BlockBand
