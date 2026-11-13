module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fin.Rev

/-!
# Eigenpairs of Hermitian matrices in increasing order

Mathlib enumerates the eigenvalues of a Hermitian matrix in decreasing order; reversing
`Fin (Fintype.card ι)` gives the eigenvalues in increasing order, with multiplicity, together
with an orthonormal eigenbasis. This file sets up this convention for complex Hermitian matrices on
any finite index type and proves the eigen-equation, orthonormality and unit total site mass of
the eigenvectors. Measurability in the matrix is treated elsewhere.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Foundations.Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℂ}

/-- The canonical rank-to-site equivalence, reversed for increasing ranks. -/
def increasingIndex : Fin (Fintype.card ι) ≃ ι :=
  Fin.revPerm.trans (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))

/-- The eigenvalues in increasing order, counted with multiplicity; rank `i` is the
`(i.val + 1)`-th smallest eigenvalue. -/
def increasingEigenvalue (hA : A.IsHermitian) (i : Fin (Fintype.card ι)) : ℝ :=
  hA.eigenvalues₀ i.rev

/-- An orthonormal eigenbasis indexed by increasing rank. -/
def increasingEigenbasis (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  hA.eigenvectorBasis.reindex increasingIndex.symm

/-- The coordinates of the eigenvector of rank `i`. -/
def increasingEigenvector (hA : A.IsHermitian) (i : Fin (Fintype.card ι)) : ι → ℂ :=
  ⇑(increasingEigenbasis hA i)

/-- `increasingEigenvalue` is monotone. -/
theorem increasingEigenvalue_monotone (hA : A.IsHermitian) :
    Monotone (increasingEigenvalue hA) := by
  intro i j hij
  exact hA.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

/-- The eigenvalue of rank `i` is Mathlib's eigenvalue at the label `increasingIndex i`. -/
theorem eigenvalue_increasingIndex (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    hA.eigenvalues (increasingIndex i) = increasingEigenvalue hA i := by
  simp [Matrix.IsHermitian.eigenvalues, increasingIndex, increasingEigenvalue]

/-- The rank-reindexed basis vector is the corresponding Mathlib eigenvector. -/
theorem increasingEigenbasis_apply (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    increasingEigenbasis hA i = hA.eigenvectorBasis (increasingIndex i) := by
  simp [increasingEigenbasis, OrthonormalBasis.reindex_apply]

/-- The eigen-equation `A v_i = λ_i v_i`. -/
theorem mulVec_increasingEigenvector (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    A.mulVec (increasingEigenvector hA i) =
      (increasingEigenvalue hA i : ℂ) • increasingEigenvector hA i := by
  unfold increasingEigenvector
  rw [increasingEigenbasis_apply, ← eigenvalue_increasingIndex]
  funext x
  simpa +instances only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal, smul_eq_mul] using
    congrFun (hA.mulVec_eigenvectorBasis (increasingIndex i)) x

/-- The eigen-equation in coordinates: `(A v_i)(x) = λ_i v_i(x)`. -/
theorem mulVec_increasingEigenvector_apply (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) (x : ι) :
    A.mulVec (increasingEigenvector hA i) x =
      (increasingEigenvalue hA i : ℂ) * increasingEigenvector hA i x := by
  simpa using congrFun (mulVec_increasingEigenvector hA i) x

/-- Orthonormality in coordinates: `Σ_x conj(v_i(x)) v_j(x) = δ_ij`. -/
theorem increasingEigenvector_orthonormal (hA : A.IsHermitian)
    (i j : Fin (Fintype.card ι)) :
    (∑ x, starRingEnd ℂ (increasingEigenvector hA i x) *
      increasingEigenvector hA j x) = if i = j then 1 else 0 := by
  have h := (increasingEigenbasis hA).inner_eq_ite i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

/-- Each eigenvector has unit total site mass `Σ_x |v_i(x)|² = 1`. -/
theorem sum_norm_sq_increasingEigenvector (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    (∑ x, ‖increasingEigenvector hA i x‖ ^ 2) = 1 := by
  unfold increasingEigenvector
  rw [← EuclideanSpace.norm_sq_eq (increasingEigenbasis hA i),
    (increasingEigenbasis hA).orthonormal.norm_eq_one]
  simp only [one_pow]

omit [DecidableEq ι] in
/-- If `Σ_x conj(v(x)) v(x) = 1` in `ℂ`, then `Σ_x |v(x)|² = 1` in `ℝ`. -/
theorem sum_norm_sq_eq_one_of_inner_sum_eq_one (v : ι → ℂ)
    (hv : (∑ x, starRingEnd ℂ (v x) * v x) = 1) :
    (∑ x, ‖v x‖ ^ 2) = 1 := by
  let u : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hu : inner ℂ u u = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact hv
  calc
    (∑ x, ‖v x‖ ^ 2) = ‖u‖ ^ 2 := (EuclideanSpace.norm_sq_eq u).symm
    _ = (inner ℂ u u).re := norm_sq_eq_re_inner (𝕜 := ℂ) u
    _ = 1 := by rw [hu]; rfl

/-- Two Hermitian matrices have the same increasing eigenvalues if and only if they have the same
characteristic polynomial. -/
theorem increasingEigenvalue_eq_iff_charpoly_eq
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    increasingEigenvalue hA = increasingEigenvalue hB ↔ A.charpoly = B.charpoly := by
  rw [← hA.eigenvalues_eq_eigenvalues_iff hB]
  constructor
  · intro h
    funext x
    let i := increasingIndex.symm x
    have hi : increasingIndex i = x := increasingIndex.apply_symm_apply x
    simpa only [← eigenvalue_increasingIndex, hi] using congrFun h i
  · intro h
    funext i
    simpa only [eigenvalue_increasingIndex] using congrFun h (increasingIndex i)

/-- Multiplication by a unit complex number preserves `|v|²`. -/
theorem norm_sq_phase_mul (z : ℂ) (hz : ‖z‖ = 1) (v : ℂ) :
    ‖z * v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_mul, hz, one_mul]

end BlockBand.Foundations.Spectral
