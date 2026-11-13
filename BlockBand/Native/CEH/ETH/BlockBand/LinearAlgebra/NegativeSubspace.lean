module

public import BlockBand.Native.CEH.ETH.BlockBand.LinearAlgebra.SylvesterInertia

/-!
# Negative-definite spectral subspaces of Hermitian matrices

This module proves the variational characterization needed for the negative part of
Sylvester's law.  The Hermitian quadratic value is strictly negative on the negative
spectral subspace, nonnegative on its complementary spectral span, and consequently any
subspace on which it is strictly negative has dimension bounded by the number of negative
eigenvalues.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- The real Hermitian quadratic value of `A` at `x`.  The inner product convention is
conjugate-linear in the first argument, so this is the real part of `xᴴ A x`. -/
def hermitianQuadraticValue
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) : ℝ :=
  RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin A x))

private theorem toEuclideanLin_eigenvector
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i) • hA.eigenvectorBasis i := by
  ext j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

private theorem inner_negativeEigenvector_sum
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (c : {i : n // hA.eigenvalues i < 0} → 𝕜) :
    inner 𝕜
        (∑ i, c i • hA.eigenvectorBasis i.1)
        (Matrix.toEuclideanLin A (∑ i, c i • hA.eigenvectorBasis i.1)) =
      ∑ i, (hA.eigenvalues i.1 : 𝕜) * (star (c i) * c i) := by
  let v : {i : n // hA.eigenvalues i < 0} → EuclideanSpace 𝕜 n :=
    fun i => hA.eigenvectorBasis i.1
  have hv : Orthonormal 𝕜 v :=
    hA.eigenvectorBasis.orthonormal.comp Subtype.val Subtype.val_injective
  calc
    inner 𝕜 (∑ i, c i • v i) (Matrix.toEuclideanLin A (∑ i, c i • v i)) =
        inner 𝕜 (∑ i, c i • v i)
          (∑ i, ((hA.eigenvalues i.1 : 𝕜) * c i) • v i) := by
            congr 1
            simp only [map_sum, LinearMapClass.map_smul, v,
              toEuclideanLin_eigenvector hA]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              c i • hA.eigenvalues i.1 • v i =
                  hA.eigenvalues i.1 • c i • v i := smul_comm _ _ _
              _ = ((hA.eigenvalues i.1 : 𝕜) * c i) • v i := by
                rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
    _ = ∑ i ∈ Finset.univ,
          star (c i) * ((hA.eigenvalues i.1 : 𝕜) * c i) :=
      hv.inner_sum c (fun i => (hA.eigenvalues i.1 : 𝕜) * c i) Finset.univ
    _ = ∑ i, (hA.eigenvalues i.1 : 𝕜) * (star (c i) * c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Spectral formula for the Hermitian quadratic value of a linear combination of the
strictly negative eigenvectors. -/
theorem hermitianQuadraticValue_negativeEigenvector_sum
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (c : {i : n // hA.eigenvalues i < 0} → 𝕜) :
    hermitianQuadraticValue A (∑ i, c i • hA.eigenvectorBasis i.1) =
      ∑ i, hA.eigenvalues i.1 * ‖c i‖ ^ 2 := by
  rw [hermitianQuadraticValue, inner_negativeEigenvector_sum hA, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RCLike.star_def, RCLike.conj_mul]
  simp

/-- The Hermitian quadratic form is strictly negative on every nonzero vector in its
negative spectral subspace.

Source: the negative-eigenspace part of the finite-dimensional spectral proof of
Sylvester's law used in the RBM eigenpair-coarea rank-sector argument.  Eigenvalues equal
to zero are excluded; the assertion contains no probabilistic parameter or limit. -/
theorem hermitianQuadraticValue_neg_of_mem_negativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x : EuclideanSpace 𝕜 n}
    (hx : x ∈ negativeSpectralSubspace hA) (hx0 : x ≠ 0) :
    hermitianQuadraticValue A x < 0 := by
  rw [negativeSpectralSubspace, Submodule.mem_span_range_iff_exists_fun 𝕜] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [hermitianQuadraticValue_negativeEigenvector_sum hA]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    apply hx0
    simp [h]
  have hnonpos : ∀ i ∈ (Finset.univ : Finset {i : n // hA.eigenvalues i < 0}),
      hA.eigenvalues i.1 * ‖c i‖ ^ 2 ≤ 0 := by
    intro i hi
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt i.property) (sq_nonneg ‖c i‖)
  have hexists : ∃ i ∈ (Finset.univ : Finset {i : n // hA.eigenvalues i < 0}),
      hA.eigenvalues i.1 * ‖c i‖ ^ 2 < 0 := by
    obtain ⟨i, hi⟩ := hc
    refine ⟨i, Finset.mem_univ i, mul_neg_of_neg_of_pos i.property ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hi)
  have hsum := (Finset.sum_neg_iff_of_nonpos hnonpos).2 hexists
  simpa using hsum

/-- The complementary spectral subspace spanned by eigenvectors with nonnegative
eigenvalue. -/
def nonnegativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Submodule.span 𝕜
    (Set.range fun i : {i : n // 0 ≤ hA.eigenvalues i} => hA.eigenvectorBasis i.1)

/-- The nonnegative eigenvectors remain linearly independent after restriction. -/
theorem nonnegativeEigenvectors_linearIndependent
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    LinearIndependent 𝕜
      (fun i : {i : n // 0 ≤ hA.eigenvalues i} => hA.eigenvectorBasis i.1) := by
  exact hA.eigenvectorBasis.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective

/-- The nonnegative spectral subspace has one dimension for each nonnegative eigenvalue. -/
theorem finrank_nonnegativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Module.finrank 𝕜 (nonnegativeSpectralSubspace hA) =
      Fintype.card {i : n // 0 ≤ hA.eigenvalues i} := by
  rw [nonnegativeSpectralSubspace,
    finrank_span_eq_card (nonnegativeEigenvectors_linearIndependent hA)]

private theorem inner_nonnegativeEigenvector_sum
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (c : {i : n // 0 ≤ hA.eigenvalues i} → 𝕜) :
    inner 𝕜
        (∑ i, c i • hA.eigenvectorBasis i.1)
        (Matrix.toEuclideanLin A (∑ i, c i • hA.eigenvectorBasis i.1)) =
      ∑ i, (hA.eigenvalues i.1 : 𝕜) * (star (c i) * c i) := by
  let v : {i : n // 0 ≤ hA.eigenvalues i} → EuclideanSpace 𝕜 n :=
    fun i => hA.eigenvectorBasis i.1
  have hv : Orthonormal 𝕜 v :=
    hA.eigenvectorBasis.orthonormal.comp Subtype.val Subtype.val_injective
  calc
    inner 𝕜 (∑ i, c i • v i) (Matrix.toEuclideanLin A (∑ i, c i • v i)) =
        inner 𝕜 (∑ i, c i • v i)
          (∑ i, ((hA.eigenvalues i.1 : 𝕜) * c i) • v i) := by
            congr 1
            simp only [map_sum, LinearMapClass.map_smul, v,
              toEuclideanLin_eigenvector hA]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              c i • hA.eigenvalues i.1 • v i =
                  hA.eigenvalues i.1 • c i • v i := smul_comm _ _ _
              _ = ((hA.eigenvalues i.1 : 𝕜) * c i) • v i := by
                rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
    _ = ∑ i ∈ Finset.univ,
          star (c i) * ((hA.eigenvalues i.1 : 𝕜) * c i) :=
      hv.inner_sum c (fun i => (hA.eigenvalues i.1 : 𝕜) * c i) Finset.univ
    _ = ∑ i, (hA.eigenvalues i.1 : 𝕜) * (star (c i) * c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Spectral formula on the nonnegative eigenvector span. -/
theorem hermitianQuadraticValue_nonnegativeEigenvector_sum
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (c : {i : n // 0 ≤ hA.eigenvalues i} → 𝕜) :
    hermitianQuadraticValue A (∑ i, c i • hA.eigenvectorBasis i.1) =
      ∑ i, hA.eigenvalues i.1 * ‖c i‖ ^ 2 := by
  rw [hermitianQuadraticValue, inner_nonnegativeEigenvector_sum hA, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RCLike.star_def, RCLike.conj_mul]
  simp

/-- The Hermitian quadratic form is nonnegative on the complementary nonnegative
spectral subspace. -/
theorem hermitianQuadraticValue_nonneg_of_mem_nonnegativeSpectralSubspace
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x : EuclideanSpace 𝕜 n}
    (hx : x ∈ nonnegativeSpectralSubspace hA) :
    0 ≤ hermitianQuadraticValue A x := by
  rw [nonnegativeSpectralSubspace, Submodule.mem_span_range_iff_exists_fun 𝕜] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [hermitianQuadraticValue_nonnegativeEigenvector_sum hA]
  exact Finset.sum_nonneg fun i _ => mul_nonneg i.property (sq_nonneg ‖c i‖)

/-- Any complex or real subspace on which the Hermitian quadratic form is strictly
negative has dimension at most the number of strictly negative eigenvalues.

This is the maximality half of the finite-dimensional variational characterization of
negative inertia.  The proof makes the given subspace disjoint from the span of the
nonnegative eigenvectors and applies the finite-dimensional dimension inequality. -/
theorem finrank_le_negativeEigenvalueCount_of_neg
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (V : Submodule 𝕜 (EuclideanSpace 𝕜 n))
    (hV : ∀ x ∈ V, x ≠ 0 → hermitianQuadraticValue A x < 0) :
    Module.finrank 𝕜 V ≤ negativeEigenvalueCount hA := by
  have hdisjoint : Disjoint V (nonnegativeSpectralSubspace hA) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have hneg := hV x hx.1 hx0
    have hnonneg := hermitianQuadraticValue_nonneg_of_mem_nonnegativeSpectralSubspace
      hA hx.2
    exact (not_lt_of_ge hnonneg) hneg
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  rw [finrank_nonnegativeSpectralSubspace hA, finrank_euclideanSpace] at hdim
  have hcard : Fintype.card {i : n // 0 ≤ hA.eigenvalues i} =
      Fintype.card n - negativeEigenvalueCount hA := by
    rw [negativeEigenvalueCount,
      ← Fintype.card_subtype (fun i : n => hA.eigenvalues i < 0)]
    simpa [not_lt] using
      (Fintype.card_subtype_compl (fun i : n => hA.eigenvalues i < 0))
  rw [hcard] at hdim
  have hcount := negativeEigenvalueCount_le_card hA
  omega

end CEHNative.BlockBand
