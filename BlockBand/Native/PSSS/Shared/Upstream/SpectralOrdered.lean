module

public import BlockBand.Model.Construction.OrderedEigenvalues

/-!
# Sorted eigenvalues of Hermitian matrices

Entrywise perturbation stability of the decreasingly sorted eigenvalues of a Hermitian matrix.
The implementation is a narrow Apache-2.0 Tau Ceti dependency closure copied from revision
`720bf8c135bd2c354a15d55a73f2fc2c3d7aa358`; it does not register Tau Ceti as a Lake package and
does not include functional calculus, Schatten norms, Gaussian probability, or unrelated Tau Ceti
modules.
-/

set_option autoImplicit false

@[expose] public section

namespace PSSSNative.Shared.Upstream.SpectralOrdered

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

end PSSSNative.Shared.Upstream.SpectralOrdered
