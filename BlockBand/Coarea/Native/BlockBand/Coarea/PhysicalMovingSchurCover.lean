module

public import BlockBand.Coarea.Native.BlockBand.Coarea.MovingSchurGlobalCover
public import BlockBand.Coarea.Native.BlockBand.Coarea.SchurData
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Physical moving-Schur interval cover

This module specializes the intervalwise crossing cover to the Schur family of a
fixed Hermitian block matrix pencil `H - E I`.  In particular, the spectral
contraction is obtained from the Loewner comparison by Courant–Fischer, rather
than supplied as a scalar branch assumption.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix Set
open scoped ComplexOrder MatrixOrder InnerProductSpace

/-- Courant–Fischer monotonicity for the project's increasingly ordered
Hermitian eigenvalues. -/
theorem orderedEigenvalue_mono_of_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : HermitianMatrix ι)
    (hAB : (A : Matrix ι ι ℂ) ≤ (B : Matrix ι ι ℂ))
    (r : Fin (Fintype.card ι)) :
    orderedEigenvalue A r ≤ orderedEigenvalue B r := by
  simp only [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.eigenvalue_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr A.property)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr B.property)
    finrank_euclideanSpace
  · intro x
    have hp : (Matrix.toEuclideanLin ((B : Matrix ι ι ℂ) - (A : Matrix ι ι ℂ))).IsPositive :=
      (Matrix.isPositive_toEuclideanLin_iff).2 (Matrix.le_iff.mp hAB)
    have hx := hp.2 x
    simp only [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub] at hx
    linarith

/-- Quantitative Courant–Fischer comparison.  A unit-vector Rayleigh
contraction by `δ` contracts every increasingly ordered eigenvalue by `δ`. -/
theorem orderedEigenvalue_contract_of_rayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₂ A₁ : HermitianMatrix ι) (δ : ℝ)
    (hquad : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 →
      RCLike.re ⟪(Matrix.toEuclideanLin (A₂ : Matrix ι ι ℂ)) x, x⟫_ℂ ≤
        RCLike.re ⟪(Matrix.toEuclideanLin (A₁ : Matrix ι ι ℂ)) x, x⟫_ℂ - δ)
    (r : Fin (Fintype.card ι)) :
    orderedEigenvalue A₂ r ≤ orderedEigenvalue A₁ r - δ := by
  simp only [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀]
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr A₂.property
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr A₁.property
  obtain ⟨V, hVdim, hVlow⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace r.rev
  obtain ⟨x, hxV, hnx, hup⟩ :=
    hS.exists_unit_vector_re_inner_le_eigenvalue
      finrank_euclideanSpace r.rev V hVdim
  calc
    hT.eigenvalues finrank_euclideanSpace r.rev ≤
        RCLike.re ⟪(Matrix.toEuclideanLin (A₂ : Matrix ι ι ℂ)) x, x⟫_ℂ :=
      hVlow x hxV hnx
    _ ≤ RCLike.re ⟪(Matrix.toEuclideanLin (A₁ : Matrix ι ι ℂ)) x, x⟫_ℂ - δ :=
      hquad x hnx
    _ ≤ hS.eigenvalues finrank_euclideanSpace r.rev - δ :=
      sub_le_sub_right hup δ

/-- A matrix Loewner estimate implies the scalar ordered-spectrum contraction
used by `MovingSchurGlobalCover`.  This is the precise Courant–Fischer bridge
for the paper's estimate `S(E₂) ≤ S(E₁) - (E₂-E₁)I`. -/
theorem orderedSpectrumContractsOn_of_loewner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ℝ → HermitianMatrix ι} {I : Set ℝ}
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      (S E₂ : Matrix ι ι ℂ) ≤
        (S E₁ : Matrix ι ι ℂ) - ((E₂ - E₁ : ℝ) : ℂ) • 1) :
    OrderedSpectrumContractsOn S I := by
  intro r E₁ hE₁ E₂ hE₂ hlt
  apply orderedEigenvalue_contract_of_rayleigh (S E₂) (S E₁) (E₂ - E₁)
  intro x hx
  have hp : (Matrix.toEuclideanLin
      (((S E₁ : Matrix ι ι ℂ) - ((E₂ - E₁ : ℝ) : ℂ) • 1) -
        (S E₂ : Matrix ι ι ℂ))).IsPositive :=
    (Matrix.isPositive_toEuclideanLin_iff).2 (Matrix.le_iff.mp
      (hloewner E₁ hE₁ E₂ hE₂ hlt))
  have hq := hp.2 x
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left, map_smul,
    LinearMap.smul_apply, inner_smul_left, RCLike.mul_re] at hq
  have hone : RCLike.re ⟪(Matrix.toEuclideanLin
      (1 : Matrix ι ι ℂ)) x, x⟫_ℂ = 1 := by
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal,
      hx]
  have hscalar : RCLike.re ((starRingEnd ℂ) ((E₂ - E₁ : ℝ) : ℂ)) = E₂ - E₁ := by
    simp
  have hscalarIm : RCLike.im ((starRingEnd ℂ) ((E₂ - E₁ : ℝ) : ℂ)) = 0 := by
    simp
  rw [hone, hscalar, hscalarIm] at hq
  norm_num at hq
  exact hq

/-- A Hermitian determinant vanishes exactly when one increasingly ordered
eigenvalue is zero. -/
theorem hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) :
    (A : Matrix ι ι ℂ).det = 0 ↔
      ∃ r : Fin (Fintype.card ι), orderedEigenvalue A r = 0 := by
  rw [A.property.det_eq_prod_eigenvalues]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    let k : Fin (Fintype.card ι) :=
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i
    refine ⟨k.rev, ?_⟩
    simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, k] using hi
  · rintro ⟨r, hr⟩
    let i : ι :=
      Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) r.rev
    refine ⟨i, ?_⟩
    simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, i] using hr

/-- The exterior block of the physical pencil `H - E I`. -/
def physicalExteriorPencil
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) (E : ℝ) : Matrix n n ℂ :=
  D - (E : ℂ) • 1

/-- The retained block of the physical pencil `H - E I`. -/
def physicalRetainedPencil
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (E : ℝ) : Matrix m m ℂ :=
  A - (E : ℂ) • 1

/-- The full physical block pencil, with the retained block first. -/
def physicalBlockPencil
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks (physicalRetainedPencil A E) B Bᴴ
    (physicalExteriorPencil D E)

/-- The blockwise definition is exactly the fixed physical Hermitian matrix
minus `E I`; no energy dependence is hidden in the coupling. -/
theorem physicalBlockPencil_eq_sub_smul_one
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) :
    physicalBlockPencil A B D E =
      Matrix.fromBlocks A B Bᴴ D -
        (E : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases hij : i = j <;>
            simp [physicalBlockPencil, physicalRetainedPencil,
              physicalExteriorPencil, hij]
      | inr j =>
          simp [physicalBlockPencil, physicalRetainedPencil,
            physicalExteriorPencil]
  | inr i =>
      cases j with
      | inl j =>
          simp [physicalBlockPencil, physicalRetainedPencil,
            physicalExteriorPencil]
      | inr j =>
          by_cases hij : i = j <;>
            simp [physicalBlockPencil, physicalRetainedPencil,
              physicalExteriorPencil, hij]

/-- The physical moving Schur family.  Mathlib's total nonsingular inverse makes
this a globally defined matrix; all determinant and kernel statements below
restrict to energies where the exterior pencil is invertible. -/
def physicalSchurMatrix
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) : Matrix m m ℂ :=
  physicalRetainedPencil A E -
    B * (physicalExteriorPencil D E)⁻¹ * Bᴴ

/-- The physical Schur family is Hermitian at every energy. -/
theorem physicalSchurMatrix_isHermitian
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (E : ℝ) :
    (physicalSchurMatrix A B D E).IsHermitian := by
  have hret : (physicalRetainedPencil A E).IsHermitian := by
    exact hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hext : (physicalExteriorPencil D E).IsHermitian := by
    exact hD.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  exact hret.sub (Matrix.isHermitian_mul_mul_conjTranspose B hext.inv)

/-- The physical moving Schur family as a family in the project's Hermitian
matrix subtype. -/
def physicalSchurFamily
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) : ℝ → HermitianMatrix m :=
  fun E => ⟨physicalSchurMatrix A B D E,
    physicalSchurMatrix_isHermitian A B D hA hD E⟩

/-- The exterior pencil as a Hermitian family. -/
def physicalExteriorFamily
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian) : ℝ → HermitianMatrix n :=
  fun E => ⟨physicalExteriorPencil D E, by
    exact hD.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))⟩

/-- The full physical pencil is Hermitian. -/
theorem physicalBlockPencil_isHermitian
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (E : ℝ) :
    (physicalBlockPencil A B D E).IsHermitian := by
  apply Matrix.isHermitian_fromBlocks_iff.mpr
  refine ⟨?_, rfl, Matrix.conjTranspose_conjTranspose B, ?_⟩
  · exact hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  · exact hD.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))

/-- The full physical pencil as a Hermitian matrix. -/
def physicalBlockHermitian
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (E : ℝ) :
    HermitianMatrix (m ⊕ n) :=
  ⟨physicalBlockPencil A B D E,
    physicalBlockPencil_isHermitian A B D hA hD E⟩

/-- The physical Schur family inherits the intervalwise contraction directly
from the physical Loewner estimate. -/
theorem physicalSchurFamily_contractsOn_of_loewner
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) {I : Set ℝ}
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1) :
    OrderedSpectrumContractsOn (physicalSchurFamily A B D hA hD) I :=
  orderedSpectrumContractsOn_of_loewner hloewner

/-- On a pole-free energy, the physical characteristic determinant factors
into the exterior determinant and the moving Schur determinant. -/
theorem det_physicalBlockPencil_eq
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)] :
    (physicalBlockPencil A B D E).det =
      (physicalExteriorPencil D E).det *
        (physicalSchurMatrix A B D E).det := by
  rw [physicalBlockPencil, Matrix.det_fromBlocks₂₂]
  simp only [physicalSchurMatrix]
  rw [Matrix.invOf_eq_nonsing_inv]

/-- Away from exterior poles, vanishing of the full physical determinant is
exactly vanishing of the physical Schur determinant. -/
theorem det_physicalBlockPencil_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)] :
    (physicalBlockPencil A B D E).det = 0 ↔
      (physicalSchurMatrix A B D E).det = 0 := by
  rw [det_physicalBlockPencil_eq A B D E]
  have hext : (physicalExteriorPencil D E).det ≠ 0 :=
    isUnit_iff_ne_zero.mp
      (Matrix.isUnit_det_of_invertible (physicalExteriorPencil D E))
  exact mul_eq_zero.trans (or_iff_right hext)

/-- Pointwise physical Schur-graph reconstruction on a pole-free interval. -/
theorem physicalBlockPencil_mulVec_schurReconstruction
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)] (v : m → ℂ) :
    physicalBlockPencil A B D E *ᵥ
        schurReconstruction Bᴴ (physicalExteriorPencil D E) v =
      (physicalSchurMatrix A B D E *ᵥ v) ⊕ᵥ (0 : n → ℂ) := by
  rw [physicalBlockPencil, physicalSchurMatrix,
    ← Matrix.invOf_eq_nonsing_inv (physicalExteriorPencil D E)]
  exact fromBlocks_mulVec_schurReconstruction
    (physicalRetainedPencil A E) B Bᴴ (physicalExteriorPencil D E) v

/-- A nonzero physical Schur null vector reconstructs to a nonzero null vector
of the full physical pencil. -/
theorem physicalSchur_reconstruct_nonzeroKernel
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)]
    {v : m → ℂ} (hv0 : v ≠ 0)
    (hv : physicalSchurMatrix A B D E *ᵥ v = 0) :
    schurReconstruction Bᴴ (physicalExteriorPencil D E) v ≠ 0 ∧
      physicalBlockPencil A B D E *ᵥ
        schurReconstruction Bᴴ (physicalExteriorPencil D E) v = 0 := by
  constructor
  · simpa [schurReconstruction] using
      (schurReconstruction_injective Bᴴ
        (physicalExteriorPencil D E)).ne hv0
  · rw [physicalBlockPencil_mulVec_schurReconstruction A B D E v, hv]
    ext i
    cases i <;> rfl

/-- Away from exterior poles, the full physical pencil has a nonzero kernel
vector exactly when its Schur complement does. -/
theorem physicalBlockPencil_nontrivialKernel_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)] :
    (∃ w ≠ 0, physicalBlockPencil A B D E *ᵥ w = 0) ↔
      ∃ v ≠ 0, physicalSchurMatrix A B D E *ᵥ v = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff,
    Matrix.exists_mulVec_eq_zero_iff,
    det_physicalBlockPencil_eq_zero_iff A B D E]

/-- At every pole-free energy, physical eigenvalue membership is exactly an
ordered crossing of the physical moving Schur family. -/
theorem physicalBlockPencil_nontrivialKernel_iff_schurCrossing
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)] :
    (∃ w ≠ 0, physicalBlockPencil A B D E *ᵥ w = 0) ↔
      ∃ r, orderedEigenvalue (physicalSchurFamily A B D hA hD E) r = 0 := by
  rw [physicalBlockPencil_nontrivialKernel_iff A B D E,
    Matrix.exists_mulVec_eq_zero_iff]
  exact hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero
    (physicalSchurFamily A B D hA hD E)

/-- Exact additive rank-sector equivalence for a physical crossing. -/
theorem physicalOrderedRank_iff_additiveSchurSector
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    (E : ℝ) [Invertible (physicalExteriorPencil D E)]
    (α : Fin (Fintype.card (m ⊕ n))) :
    orderedZeroRank (physicalBlockHermitian A B D hA hD E).property = α.val + 1 ↔
      negativeEigenvalueCount (physicalExteriorFamily D hD E).property +
        negativeEigenvalueCount (physicalSchurFamily A B D hA hD E).property + 1 =
          α.val + 1 := by
  have h := orderedZeroRank_fromBlocks_eq_iff
    (physicalRetainedPencil A E) B (physicalExteriorPencil D E)
    (by exact hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E)))
    (physicalExteriorFamily D hD E).property α
  dsimp only at h ⊢
  convert h using 1 <;>
    simp [physicalBlockHermitian, physicalBlockPencil,
      physicalSchurFamily, physicalSchurMatrix, Matrix.invOf_eq_nonsing_inv]
  apply iff_of_eq
  congr 1

/-- Physical eigen-energies in one fixed ordered-rank sector.  The rank is the
one-based rank of the zero in the full Hermitian pencil. -/
abbrev PhysicalFixedRankEigenEnergy
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n))) :=
  {E : ℝ // E ∈ I ∧
    (∃ w ≠ 0, physicalBlockPencil A B D E *ᵥ w = 0) ∧
      orderedZeroRank (physicalBlockHermitian A B D hA hD E).property = α.val + 1}

/-- Forgetting the branch label sends an additive-sector Schur crossing to the
corresponding physical full-pencil eigenvalue. -/
def physicalFixedRankEigenEnergyMap
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n)))
    (hpoleFree : ∀ E ∈ I, IsUnit (physicalExteriorPencil D E).det) :
    MovingFixedRankSchurCrossing (physicalSchurFamily A B D hA hD) I
      (fun E => negativeEigenvalueCount (physicalExteriorFamily D hD E).property) α.val →
      PhysicalFixedRankEigenEnergy A B D hA hD I α := by
  intro p
  letI : Invertible (physicalExteriorPencil D p.1.2) :=
    invertibleOfIsUnitDet _ (hpoleFree p.1.2 p.2.1)
  refine ⟨p.1.2, p.2.1, ?_, ?_⟩
  · rw [physicalBlockPencil_nontrivialKernel_iff_schurCrossing A B D hA hD p.1.2]
    exact ⟨p.1.1, p.2.2.1⟩
  · exact (physicalOrderedRank_iff_additiveSchurSector
      A B D hA hD p.1.2 α).2 p.2.2.2

/-- On a pole-free simple-spectrum interval, every physical eigenvalue in the
fixed full ordered-rank sector is represented by exactly one ordered Schur
branch crossing. -/
theorem physicalFixedRankEigenEnergyMap_bijective
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n)))
    (hpoleFree : ∀ E ∈ I, IsUnit (physicalExteriorPencil D E).det)
    (hsimple : ∀ E ∈ I,
      Function.Injective (orderedEigenvalue (physicalSchurFamily A B D hA hD E))) :
    Function.Bijective
      (physicalFixedRankEigenEnergyMap A B D hA hD I α hpoleFree) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · have hE : p.1.2 = q.1.2 := congrArg Subtype.val hpq
      apply hsimple p.1.2 p.2.1
      rw [p.2.2.1]
      simpa [hE] using q.2.2.1.symm
    · exact congrArg Subtype.val hpq
  · intro E
    let : Invertible (physicalExteriorPencil D E.1) :=
      invertibleOfIsUnitDet _ (hpoleFree E.1 E.2.1)
    have hcross : ∃ r,
        orderedEigenvalue (physicalSchurFamily A B D hA hD E.1) r = 0 :=
      (physicalBlockPencil_nontrivialKernel_iff_schurCrossing
        A B D hA hD E.1).1 E.2.2.1
    have hrank :
        negativeEigenvalueCount (physicalExteriorFamily D hD E.1).property +
          negativeEigenvalueCount (physicalSchurFamily A B D hA hD E.1).property + 1 =
            α.val + 1 :=
      (physicalOrderedRank_iff_additiveSchurSector
        A B D hA hD E.1 α).1 E.2.2.2
    rcases hcross with ⟨r, hr⟩
    refine ⟨⟨(r, E.1), E.2.1, hr, hrank⟩, ?_⟩
    exact Subtype.ext rfl

/-- Complete physical interval cover.  The first conclusion is unique
representation of every full-pencil eigenvalue in the additive fixed-rank
sector.  The second says a fixed ordered Schur branch crosses at most once on
the pole interval. -/
theorem physicalMovingSchur_globalCover
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (I : Set ℝ)
    (α : Fin (Fintype.card (m ⊕ n)))
    (hpoleFree : ∀ E ∈ I, IsUnit (physicalExteriorPencil D E).det)
    (hloewner : ∀ E₁ ∈ I, ∀ E₂ ∈ I, E₁ < E₂ →
      physicalSchurMatrix A B D E₂ ≤
        physicalSchurMatrix A B D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ E ∈ I,
      Function.Injective (orderedEigenvalue (physicalSchurFamily A B D hA hD E))) :
    Function.Bijective
        (physicalFixedRankEigenEnergyMap A B D hA hD I α hpoleFree) ∧
      ∀ p q : MovingFixedRankSchurCrossing
          (physicalSchurFamily A B D hA hD) I
          (fun E => negativeEigenvalueCount (physicalExteriorFamily D hD E).property) α.val,
        p.1.1 = q.1.1 → p.1.2 = q.1.2 := by
  refine ⟨physicalFixedRankEigenEnergyMap_bijective
    A B D hA hD I α hpoleFree hsimple, ?_⟩
  intro p q hr
  exact orderedSchurBranch_zero_unique
    (physicalSchurFamily_contractsOn_of_loewner A B D hA hD hloewner)
    p.2.1 q.2.1 p.2.2.1 (hr ▸ q.2.2.1)

end CoareaNative.BlockBand
