module

public import BlockBand.Model.Construction.OrderedEigenvalues
public import BlockBand.Model.Construction.OrderedSubmodule

/-!
# Sorted eigenvalues of Hermitian matrices

Finite-dimensional facts about the decreasingly sorted eigenvalues of a Hermitian matrix:
stability under entrywise and operator-norm perturbations, and the rank as the number of nonzero
sorted eigenvalues. The implementation is a narrow Apache-2.0 Tau Ceti dependency closure copied
from revision `720bf8c135bd2c354a15d55a73f2fc2c3d7aa358`; it does not register Tau Ceti as a
Lake package and does not include functional calculus, Schatten norms, Gaussian probability, or
unrelated Tau Ceti modules.
-/

set_option autoImplicit false

@[expose] public section

namespace CEHNative.Shared.Upstream.SpectralOrdered

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {A B : Matrix ι ι 𝕜}

/-- An entrywise perturbation changes each decreasing sorted eigenvalue by at most
`card ι * ε`. -/
theorem sortedEigenvalueEntrywisePerturbation
    (hA : A.IsHermitian) (hB : B.IsHermitian) {ε : ℝ}
    (hentry : ∀ i j, ‖A i j - B i j‖ ≤ ε) (k : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ (Fintype.card ι : ℝ) * ε :=
  hA.abs_eigenvalues₀_sub_le_of_entry_le hB hentry k

/-- An entrywise bound controls each decreasing sorted eigenvalue. -/
theorem sortedEigenvalueEntrywiseBound (hA : A.IsHermitian) {β : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ β) (k : Fin (Fintype.card ι)) :
    |hA.eigenvalues₀ k| ≤ (Fintype.card ι : ℝ) * β :=
  hA.abs_eigenvalues₀_le_of_entry_le hentry k

/-- A smaller Euclidean operator perturbation preserves a threshold comparison. -/
theorem sortedEigenvalueThresholdStable
    (hA : A.IsHermitian) (hB : B.IsHermitian) {c : ℝ}
    (i : Fin (Fintype.card ι))
    (hgap : ‖A - B‖ < |hA.eigenvalues₀ i - c|) :
    c ≤ hB.eigenvalues₀ i ↔ c ≤ hA.eigenvalues₀ i :=
  hA.le_eigenvalues₀_iff_of_norm_sub_lt hB i hgap

/-- Hermitian rank is the multiplicity count of nonzero sorted eigenvalues. -/
theorem hermitianRankEqCardNonzeroSortedEigenvalues (hA : A.IsHermitian) :
    A.rank = Fintype.card {i : Fin (Fintype.card ι) // hA.eigenvalues₀ i ≠ 0} :=
  hA.rank_eq_card_non_zero_eigenvalues₀

end CEHNative.Shared.Upstream.SpectralOrdered
