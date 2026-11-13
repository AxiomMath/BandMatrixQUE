module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.CodimensionOneInterlacing
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Spectrum of a codimension-one orthogonal compression

This module isolates the exact unitary block decomposition of the ambient
compression.  The ambient operator has one distinguished zero block and its
other block is the restriction to the orthogonal complement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open scoped ComplexConjugate Matrix

universe u v

/-- The canonical unitary identification of a scalar coordinate and the
orthogonal complement of a unit vector with the ambient Hilbert space. -/
def unitarySpanOrthogonal {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (ℂ × (ℂ ∙ u)ᗮ) ≃ₗᵢ[ℂ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.toSpanUnitSingleton u hu)
      (LinearIsometryEquiv.refl ℂ (ℂ ∙ u)ᗮ)).trans
    ((ℂ ∙ u).orthogonalDecomposition.symm)

/-- The orthogonal block has the expected codimension-one dimension. -/
theorem finrank_spanOrthogonal_eq_card_sub_one {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    Module.finrank ℂ (ℂ ∙ u)ᗮ = Fintype.card ι - 1 := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (ℂ ∙ u)
  rw [finrank_span_singleton hu0, finrank_euclideanSpace] at hdim
  omega

/-- The compression, as an endomorphism of `u⊥`. -/
def compressionRestriction {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (ℂ ∙ u)ᗮ →ₗ[ℂ] (ℂ ∙ u)ᗮ :=
  LinearMap.codRestrict ((ℂ ∙ u)ᗮ)
    ((Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ)).comp
      ((ℂ ∙ u)ᗮ).subtype)
    (by
      intro x
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact inner_orthogonalCompression_apply_unit K hu x)

@[simp] theorem compressionRestriction_apply {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (x : (ℂ ∙ u)ᗮ) :
    (compressionRestriction K u hu x : EuclideanSpace ℂ ι) =
      Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ) x :=
  rfl

/-- The compression on `u⊥` is symmetric. -/
theorem compressionRestriction_isSymmetric {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (compressionRestriction K u hu).IsSymmetric := by
  let T := Matrix.toEuclideanLin
    (orthogonalCompression K u : Matrix ι ι ℂ)
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (orthogonalCompression K u).2
  have hInv : ∀ x ∈ (ℂ ∙ u)ᗮ, T x ∈ (ℂ ∙ u)ᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_orthogonalCompression_apply_unit K hu x
  exact hT.restrict_invariant hInv

/-- The ordinary-product linear equivalence underlying the unitary coordinates. -/
def spanOrthogonalLinearEquiv {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (u : E) (hu : ‖u‖ = 1) : (ℂ × (ℂ ∙ u)ᗮ) ≃ₗ[ℂ] E :=
  (WithLp.linearEquiv 2 ℂ (ℂ × (ℂ ∙ u)ᗮ)).symm.trans
    (unitarySpanOrthogonal u hu).toLinearEquiv

@[simp] theorem spanOrthogonalLinearEquiv_apply {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (u : E) (hu : ‖u‖ = 1) (z : ℂ) (x : (ℂ ∙ u)ᗮ) :
    spanOrthogonalLinearEquiv u hu (z, x) = z • u + x := by
  rfl

/-- The ambient compression is linearly conjugate to the direct sum of one
zero scalar block and the codimension-one compression. -/
theorem orthogonalCompression_eq_conj_prodMap {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ) =
      (spanOrthogonalLinearEquiv u hu).conj
        ((0 : ℂ →ₗ[ℂ] ℂ).prodMap (compressionRestriction K u hu)) := by
  apply LinearMap.ext
  intro y
  let e := spanOrthogonalLinearEquiv u hu
  generalize hq : e.symm y = q
  obtain ⟨z, x⟩ := q
  have hy : y = e (z, x) := by
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e (z, x) := congrArg e hq
  rw [hy]
  change Matrix.toEuclideanLin
      (orthogonalCompression K u : Matrix ι ι ℂ) (e (z, x)) =
    e (((0 : ℂ →ₗ[ℂ] ℂ).prodMap (compressionRestriction K u hu))
      (e.symm (e (z, x))))
  rw [e.symm_apply_apply, LinearMap.prodMap_apply]
  simp only [e, spanOrthogonalLinearEquiv_apply, LinearMap.zero_apply]
  change Matrix.toEuclideanLin
      (orthogonalCompression K u : Matrix ι ι ℂ) (z • u + x) =
    0 • u + (compressionRestriction K u hu x : EuclideanSpace ℂ ι)
  rw [map_add, map_smul, orthogonalCompression_apply_unit_eq_zero K hu]
  simp

/-- Exact characteristic-polynomial identity: the ambient compression has
precisely the restriction spectrum together with one zero, counted
with algebraic multiplicity. -/
theorem orthogonalCompression_charpoly_eq_X_mul_restriction {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (Matrix.toEuclideanLin
        (orthogonalCompression K u : Matrix ι ι ℂ)).charpoly =
      Polynomial.X * (compressionRestriction K u hu).charpoly := by
  rw [orthogonalCompression_eq_conj_prodMap K u hu]
  rw [(spanOrthogonalLinearEquiv u hu).charpoly_conj]
  rw [LinearMap.charpoly_prodMap]
  simp

/-- Exact multiset form of the extra-zero spectral identity. -/
theorem orthogonalCompression_roots_charpoly_eq_zero_cons_restriction {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (Matrix.toEuclideanLin
        (orthogonalCompression K u : Matrix ι ι ℂ)).charpoly.roots =
      {0} + (compressionRestriction K u hu).charpoly.roots := by
  rw [orthogonalCompression_charpoly_eq_X_mul_restriction K u hu]
  rw [Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero
    (LinearMap.charpoly_monic (compressionRestriction K u hu)).ne_zero)]
  simp

end PSSSNative.BlockBand.PSSS
