module

public import BlockBand.Coarea.Native.Shared.Upstream.SpectralOrdered

/-!
# Increasing Hermitian eigenvalues, inertia, and counts

`eigenCount A s` is a `Nat`-valued multiplicity count over the finite ordered
enumeration, and `inertia A` counts strictly negative eigenvalues via
`Set.Iio 0`. The deterministic perturbation facts preserve Mathlib's
entrywise and L²-operator normalizations exactly.  Measurability is treated
separately.
-/

set_option autoImplicit false

@[expose] public section

namespace CoareaNative.BlockBand

open scoped ComplexOrder Matrix.Norms.L2Operator
open CoareaNative.Shared.Upstream.SpectralOrdered

/-- Finite complex Hermitian matrices with the subtype
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

/-- The defining increasing/decreasing reindexing. -/
theorem orderedEigenvalue_def (A : HermitianMatrix ι)
    (i : Fin (Fintype.card ι)) :
    orderedEigenvalue A i = A.property.eigenvalues₀ i.rev := rfl

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

/-- An entrywise bound controls each increasing ordered eigenvalue. -/
theorem orderedEigenvalue_entrywiseBound
    (A : HermitianMatrix ι) {β : ℝ}
    (hentry : ∀ i j, ‖(A : Matrix ι ι ℂ) i j‖ ≤ β)
    (k : Fin (Fintype.card ι)) :
    |orderedEigenvalue A k| ≤ (Fintype.card ι : ℝ) * β :=
  sortedEigenvalueEntrywiseBound A.property hentry k.rev

/-- If an L²-operator perturbation is smaller than the distance of one ordered
eigenvalue to a threshold, that eigenvalue stays on the same side of the
closed upper threshold. -/
theorem orderedEigenvalue_thresholdStable
    (A B : HermitianMatrix ι) {c : ℝ} (i : Fin (Fintype.card ι))
    (hgap : ‖(A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ)‖ <
      |orderedEigenvalue A i - c|) :
    c ≤ orderedEigenvalue B i ↔ c ≤ orderedEigenvalue A i :=
  sortedEigenvalueThresholdStable A.property B.property i.rev hgap

end OrderedEigenvalues

section Counts

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplicity-counted number of increasing ordered eigenvalues in a set. -/
noncomputable def eigenCount (A : HermitianMatrix ι) (s : Set ℝ) : ℕ := by
  classical
  exact Finset.card (Finset.univ.filter fun i => orderedEigenvalue A i ∈ s)

/-- Negative inertia: the number of strictly negative eigenvalues, with
multiplicity. Zero eigenvalues do not contribute. -/
noncomputable def inertia (A : HermitianMatrix ι) : ℕ :=
  eigenCount A (Set.Iio 0)

/-- The defining finite-filter formula for eigenvalue counts. -/
theorem eigenCount_def (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s = (Finset.univ.filter fun i => orderedEigenvalue A i ∈ s).card := by
  classical
  rfl

/-- Negative inertia is the count in the strict lower half-line. -/
theorem inertia_def (A : HermitianMatrix ι) :
    inertia A = eigenCount A (Set.Iio 0) := rfl

/-- The empty set contains no eigenvalues. -/
@[simp] theorem eigenCount_empty (A : HermitianMatrix ι) : eigenCount A ∅ = 0 := by
  simp [eigenCount]

/-- The universal set contains every eigenvalue, including in the empty-matrix case. -/
@[simp] theorem eigenCount_univ (A : HermitianMatrix ι) :
    eigenCount A Set.univ = Fintype.card ι := by
  simp [eigenCount]

/-- Eigenvalue counts are monotone in the counted set. -/
theorem eigenCount_mono (A : HermitianMatrix ι) {s t : Set ℝ} (hst : s ⊆ t) :
    eigenCount A s ≤ eigenCount A t := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hst hi

/-- Equal sets give equal counts. -/
theorem eigenCount_congr (A : HermitianMatrix ι) {s t : Set ℝ} (hst : s = t) :
    eigenCount A s = eigenCount A t := by
  subst t
  rfl

/-- A singleton has zero multiplicity count exactly when no ordered
eigenvalue equals its point. -/
theorem eigenCount_singleton_eq_zero_iff (A : HermitianMatrix ι) (e : ℝ) :
    eigenCount A {e} = 0 ↔ ∀ i, orderedEigenvalue A i ≠ e := by
  classical
  simp [eigenCount]

/-- The count of nonzero increasing ordered eigenvalues is the matrix rank. -/
theorem eigenCount_ne_zero_eq_rank (A : HermitianMatrix ι) :
    eigenCount A {x | x ≠ 0} = (A : Matrix ι ι ℂ).rank := by
  classical
  rw [eigenCount_def]
  simp only [Set.mem_ofPred_eq]
  have hcard :
      (Finset.univ.filter fun i => orderedEigenvalue A i ≠ 0).card =
        (Finset.univ.filter fun i => A.property.eigenvalues₀ i ≠ 0).card := by
    apply Finset.card_bij (fun i _ => i.rev)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    · intro i _ j _ hij
      exact Fin.rev_injective hij
    · intro j hj
      refine ⟨j.rev, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        simpa [orderedEigenvalue] using hj
      · exact Fin.rev_involutive j
  rw [hcard]
  calc
    (Finset.univ.filter fun i => A.property.eigenvalues₀ i ≠ 0).card =
        Fintype.card {i : Fin (Fintype.card ι) // A.property.eigenvalues₀ i ≠ 0} :=
      (Fintype.card_subtype fun i : Fin (Fintype.card ι) =>
        A.property.eigenvalues₀ i ≠ 0).symm
    _ = (A : Matrix ι ι ℂ).rank :=
      (hermitianRankEqCardNonzeroSortedEigenvalues A.property).symm

/-- Inertia is bounded by the matrix dimension. -/
theorem inertia_le_card (A : HermitianMatrix ι) : inertia A ≤ Fintype.card ι := by
  rw [inertia_def, ← eigenCount_univ A]
  exact eigenCount_mono A (Set.subset_univ _)

/-- A uniform spectral gap and smaller L²-operator perturbation preserve the
multiplicity count in a closed upper half-line. -/
theorem eigenCount_Ici_stable
    (A B : HermitianMatrix ι) {c δ : ℝ}
    (hgap : ∀ i, δ ≤ |orderedEigenvalue A i - c|)
    (hpert : ‖(A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ)‖ < δ) :
    eigenCount B (Set.Ici c) = eigenCount A (Set.Ici c) := by
  classical
  unfold eigenCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ici]
  exact orderedEigenvalue_thresholdStable A B i (hpert.trans_le (hgap i))

/-- A uniform gap from zero and smaller L²-operator perturbation preserve
negative inertia. -/
theorem inertia_stable
    (A B : HermitianMatrix ι) {δ : ℝ}
    (hgap : ∀ i, δ ≤ |orderedEigenvalue A i|)
    (hpert : ‖(A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ)‖ < δ) :
    inertia B = inertia A := by
  classical
  unfold inertia eigenCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio]
  have h := orderedEigenvalue_thresholdStable A B (c := 0) i
    (by simpa using hpert.trans_le (hgap i))
  simpa only [not_le] using not_congr h

end Counts

end CoareaNative.BlockBand
