module

public import BlockBand.Native.CEH.ETH.BlockBand.LinearAlgebra.NegativeSubspace
public import BlockBand.Native.CEH.ETH.BlockBand.LinearAlgebra.SchurCongruence

/-!
# Sylvester invariance for finite Hermitian matrices

Sylvester's law of inertia for the negative eigenvalue count of a finite Hermitian matrix, its
additivity over block-diagonal matrices, and the inertia identity for a Schur complement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- Hermitian quadratic values transform by pullback under matrix congruence. -/
theorem hermitianQuadraticValue_congruence
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A U : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    hermitianQuadraticValue (Uᴴ * A * U) x =
      hermitianQuadraticValue A (Matrix.toEuclideanLin U x) := by
  unfold hermitianQuadraticValue
  let b := (EuclideanSpace.basisFun n 𝕜).toBasis
  change RCLike.re (inner 𝕜 x (Matrix.toLin b b (Uᴴ * A * U) x)) = _
  rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b,
    Matrix.toLin_conjTranspose]
  rw [LinearMap.adjoint_inner_right]
  rfl

/-- One direction of Sylvester invariance: an invertible congruence cannot increase the
negative eigenvalue count. -/
theorem negativeEigenvalueCount_congruence_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A U : Matrix n n 𝕜} (hA : A.IsHermitian) (hU : IsUnit U) :
    let hConj : (Uᴴ * A * U).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul U hA
    negativeEigenvalueCount hConj ≤ negativeEigenvalueCount hA := by
  dsimp only
  let hConj : (Uᴴ * A * U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U hA
  let f : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := Matrix.toEuclideanLin U
  have hf : Function.Injective f := by
    intro x y hxy
    have hraw : U *ᵥ ⇑x = U *ᵥ ⇑y := by
      exact congrArg (fun z : EuclideanSpace 𝕜 n => ⇑z) hxy
    have hcoe := Matrix.mulVec_injective_of_isUnit hU hraw
    ext i
    exact congrFun hcoe i
  let V := negativeSpectralSubspace hConj
  let W := LinearMap.range (f.domRestrict V)
  have hWneg : ∀ y ∈ W, y ≠ 0 → hermitianQuadraticValue A y < 0 := by
    intro y hy hy0
    obtain ⟨x, rfl⟩ := hy
    change hermitianQuadraticValue A (Matrix.toEuclideanLin U (x : EuclideanSpace 𝕜 n)) < 0
    rw [← hermitianQuadraticValue_congruence A U]
    apply hermitianQuadraticValue_neg_of_mem_negativeSpectralSubspace hConj x.property
    intro hx0
    apply hy0
    simp [hx0]
  have hmax := finrank_le_negativeEigenvalueCount_of_neg hA W hWneg
  have hrestrict : Function.Injective (f.domRestrict V) := by
    intro x y hxy
    exact Subtype.ext (hf hxy)
  have hrank := LinearMap.finrank_range_of_inj hrestrict
  calc
    negativeEigenvalueCount hConj = Module.finrank 𝕜 V :=
      (finrank_negativeSpectralSubspace hConj).symm
    _ = Module.finrank 𝕜 W := hrank.symm
    _ ≤ negativeEigenvalueCount hA := hmax

/-- **Sylvester's law of inertia**, negative part: the number of strictly negative
eigenvalues of a finite Hermitian matrix is invariant under congruence by an invertible
matrix. -/
theorem negativeEigenvalueCount_congruence
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A U : Matrix n n 𝕜} (hA : A.IsHermitian) (hU : IsUnit U) :
    let hConj : (Uᴴ * A * U).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul U hA
    negativeEigenvalueCount hConj = negativeEigenvalueCount hA := by
  dsimp only
  let hConj : (Uᴴ * A * U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U hA
  apply le_antisymm (negativeEigenvalueCount_congruence_le hA hU)
  let f : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := Matrix.toEuclideanLin U
  have hf : Function.Injective f := by
    intro x y hxy
    have hraw : U *ᵥ ⇑x = U *ᵥ ⇑y := by
      exact congrArg (fun z : EuclideanSpace 𝕜 n => ⇑z) hxy
    have hcoe := Matrix.mulVec_injective_of_isUnit hU hraw
    ext i
    exact congrFun hcoe i
  have hfsurj : Function.Surjective f := LinearMap.surjective_of_injective hf
  let e : EuclideanSpace 𝕜 n ≃ₗ[𝕜] EuclideanSpace 𝕜 n :=
    LinearEquiv.ofBijective f ⟨hf, hfsurj⟩
  let V := negativeSpectralSubspace hA
  let W := LinearMap.range (e.symm.toLinearMap.domRestrict V)
  have hWneg : ∀ y ∈ W, y ≠ 0 → hermitianQuadraticValue (Uᴴ * A * U) y < 0 := by
    intro y hy hy0
    obtain ⟨x, rfl⟩ := hy
    change hermitianQuadraticValue (Uᴴ * A * U)
      (e.symm (x : EuclideanSpace 𝕜 n)) < 0
    rw [hermitianQuadraticValue_congruence A U]
    change hermitianQuadraticValue A (e (e.symm (x : EuclideanSpace 𝕜 n))) < 0
    rw [e.apply_symm_apply]
    apply hermitianQuadraticValue_neg_of_mem_negativeSpectralSubspace hA x.property
    intro hx0
    apply hy0
    simp [hx0]
  have hmax := finrank_le_negativeEigenvalueCount_of_neg hConj W hWneg
  have hrestrict : Function.Injective (e.symm.toLinearMap.domRestrict V) := by
    intro x y hxy
    exact Subtype.ext (e.symm.injective hxy)
  have hrank := LinearMap.finrank_range_of_inj hrestrict
  calc
    negativeEigenvalueCount hA = Module.finrank 𝕜 V :=
      (finrank_negativeSpectralSubspace hA).symm
    _ = Module.finrank 𝕜 W := hrank.symm
    _ ≤ negativeEigenvalueCount hConj := hmax

/-- The negative eigenvalue count can equivalently be read from the roots of the
characteristic polynomial, with multiplicity. -/
theorem negativeEigenvalueCount_eq_card_filter_roots
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    negativeEigenvalueCount hA =
      (A.charpoly.roots.filter fun z => RCLike.re z < 0).card := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  unfold negativeEigenvalueCount
  rw [Multiset.filter_map]
  simp only [Function.comp_apply, RCLike.ofReal_re, Multiset.card_map]
  rw [← Finset.filter_val]
  rfl

/-- The negative eigenvalue count of a Hermitian block-diagonal matrix is the sum of
those of its diagonal blocks. -/
theorem negativeEigenvalueCount_fromBlocks_zero
    {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix m m 𝕜} {D : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    let hBlock : (Matrix.fromBlocks A 0 0 D).IsHermitian := by
      rw [Matrix.isHermitian_fromBlocks_iff]
      exact ⟨hA, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hD⟩
    negativeEigenvalueCount hBlock =
      negativeEigenvalueCount hA + negativeEigenvalueCount hD := by
  dsimp only
  let hBlock : (Matrix.fromBlocks A 0 0 D).IsHermitian := by
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hA, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hD⟩
  rw [negativeEigenvalueCount_eq_card_filter_roots hBlock,
    negativeEigenvalueCount_eq_card_filter_roots hA,
    negativeEigenvalueCount_eq_card_filter_roots hD]
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  rw [Polynomial.roots_mul]
  · simp only [Multiset.filter_add, Multiset.card_add]
  · exact mul_ne_zero (Matrix.charpoly_monic A).ne_zero (Matrix.charpoly_monic D).ne_zero

/-- A Hermitian matrix split into retained and exterior coordinates has negative count
 equal to the sum of the negative counts of its Schur complement and exterior block.
This is the finite-dimensional inertia identity used after the Schur graph reduction;
there are no probabilistic parameters or limiting operations. -/
theorem negativeEigenvalueCount_hermitianSchur
    {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix m m 𝕜) (B : Matrix m n 𝕜)
    (D : Matrix n n 𝕜) [Invertible D]
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
    let hInv : (⅟D).IsHermitian := by
      rw [Matrix.invOf_eq_nonsing_inv D]
      exact hD.inv
    let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
    negativeEigenvalueCount hFull =
      negativeEigenvalueCount hSchur + negativeEigenvalueCount hD := by
  dsimp only
  let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
    Matrix.isHermitian_fromBlocks_iff.mpr
      ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
  let hInv : (⅟D).IsHermitian := by
    rw [Matrix.invOf_eq_nonsing_inv D]
    exact hD.inv
  let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
    hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
  let U : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    Matrix.fromBlocks 1 0 (-(⅟D * Bᴴ)) 1
  let _ : Invertible (1 : Matrix m m 𝕜) := invertibleOne
  let _ : Invertible (1 : Matrix n n 𝕜) := invertibleOne
  let _ : Invertible U :=
    Matrix.fromBlocksZero₁₂Invertible (1 : Matrix m m 𝕜) (-(⅟D * Bᴴ))
      (1 : Matrix n n 𝕜)
  have hU : IsUnit U := isUnit_of_invertible U
  let hConj : (Uᴴ * Matrix.fromBlocks A B Bᴴ D * U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U hFull
  have hCong : negativeEigenvalueCount hConj = negativeEigenvalueCount hFull :=
    negativeEigenvalueCount_congruence hFull hU
  have hEq : Uᴴ * Matrix.fromBlocks A B Bᴴ D * U =
      Matrix.fromBlocks (A - B * ⅟D * Bᴴ) 0 0 D :=
    hermitianSchur_congruence A B D hD
  let hBlock : (Matrix.fromBlocks (A - B * ⅟D * Bᴴ) 0 0 D).IsHermitian := by
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hSchur, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hD⟩
  have hCountEq : negativeEigenvalueCount hConj = negativeEigenvalueCount hBlock :=
    negativeEigenvalueCount_eq_of_charpoly_eq hConj hBlock
      (congrArg Matrix.charpoly hEq)
  calc
    negativeEigenvalueCount hFull = negativeEigenvalueCount hConj := hCong.symm
    _ = negativeEigenvalueCount hBlock := hCountEq
    _ = negativeEigenvalueCount hSchur + negativeEigenvalueCount hD :=
      negativeEigenvalueCount_fromBlocks_zero hSchur hD

end CEHNative.BlockBand
