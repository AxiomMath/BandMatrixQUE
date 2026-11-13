module

public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.HermitianInertia
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Negative spectral subspace of a finite Hermitian matrix

This module begins the finite-dimensional Sylvester-law layer needed after the Hermitian
Schur congruence.  It isolates the span of the eigenvectors with strictly negative
eigenvalue and identifies its dimension with `negativeEigenvalueCount`.  This gives the
canonical candidate for the maximal negative-definite subspace; congruence invariance and
block-diagonal additivity can then be reduced to the corresponding maximality statement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- The negative spectral subspace of a finite Hermitian matrix: the span of those vectors
in Mathlib's orthonormal eigenbasis whose eigenvalue is strictly negative.

Source: the finite-dimensional spectral decomposition underlying Sylvester's law in the
RBM eigenpair-coarea rank-sector argument.  Zero eigenvalues are excluded, multiplicity is
retained through the eigenbasis index, and there are no probabilistic parameters,
uniformities, or limiting operations. -/
def negativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Submodule.span 𝕜
    (Set.range fun i : {i : n // hA.eigenvalues i < 0} => hA.eigenvectorBasis i.1)

/-- The eigenvectors indexed by the strictly negative eigenvalues remain linearly
independent after restriction from the full orthonormal eigenbasis. -/
theorem negativeEigenvectors_linearIndependent
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    LinearIndependent 𝕜
      (fun i : {i : n // hA.eigenvalues i < 0} => hA.eigenvectorBasis i.1) := by
  exact hA.eigenvectorBasis.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective

/-- The dimension of the negative spectral subspace is exactly the number of strictly
negative eigenvalues, counted with multiplicity.

This is the dependency-complete spectral-dimension precursor to the variational
characterization of inertia used in Sylvester congruence invariance. -/
theorem finrank_negativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Module.finrank 𝕜 (negativeSpectralSubspace hA) = negativeEigenvalueCount hA := by
  rw [negativeSpectralSubspace,
    finrank_span_eq_card (negativeEigenvectors_linearIndependent hA)]
  simpa [negativeEigenvalueCount] using
    (Fintype.card_subtype (fun i : n => hA.eigenvalues i < 0))

end CoareaNative.BlockBand
