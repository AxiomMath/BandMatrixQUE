module

public import BlockBand.Coarea.Native.BlockBand.Basic.Indices
public import Mathlib.Data.Matrix.Composition
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Block decomposition of site matrices: trace, adjoint, rank, positivity

This file sets up the block matrix notation on top of the site API. A matrix on
`ℂ^{Λ_{n,W}}`, `Λ_{n,W} = (ℤ/nℤ) × {1,…,W}`, is indexed by
`Site n W = ZMod n × Fin W`, **block label first**. Its `(k, ℓ)` block is the
`W × W` matrix `H_{I_k I_ℓ}` with entries `H_{(k,a),(ℓ,d)}`.

* `blockDecomp` is the exact (no normalization) reindexing
  `Matrix (Site n W) (Site n W) R ≃ Matrix (ZMod n) (ZMod n) (Matrix (Fin W) (Fin W) R)`,
  namely the inverse of Mathlib's `Matrix.comp`. Its `(k, ℓ)` block is the
  submatrix along the block embeddings `blockEmb k`, `blockEmb ℓ`.
* `trace_block`: the **unnormalized** trace `Tr` is
  the sum of the unnormalized traces of the diagonal blocks.
* `blockAdjoint`: `(H^*)_{I_k I_ℓ} = (H_{I_ℓ I_k})^*`; for Hermitian `H` the
  reverse bond `H_{I_{k+1} I_k}` is the adjoint of the forward bond
  `H_{I_k I_{k+1}}`.
* `restrictBlocks S T H` is `H_{ST}` for sets `S, T` of block labels, and
  `splitEquiv S` realises the decomposition `S ⊕ R`, `R = Sᶜ`
  (as in the block equations of the coarea proof, or `H_0 = K ⊕ H_{K^cK^c}` in the
  counting argument), with `H` written as `fromBlocks`.
* Rank and positivity transfer to blocks and through the split.

Finite sums (matrix products, traces) take an explicit `[NeZero n]`; no global
`NeZero` instance exists (install `Params.neZero_n` with `haveI`). Algebra is
stated over a general coefficient type wherever Mathlib allows it.

Schur complements, inverses, determinants, norms, the normalized trace, the Loewner
order, eigenvalues and masses are not treated here.
-/

@[expose] public section

set_option autoImplicit false

namespace CoareaNative.BlockBand

open Matrix

variable {n W : ℕ} {R : Type*}

/-!
### Site matrices and block arrays
-/

/-- A matrix on `R^{Λ_{n,W}}` in site coordinates, rows and
columns indexed by `Site n W = ZMod n × Fin W` (block label first). -/
abbrev SiteMatrix (n W : ℕ) (R : Type*) := Matrix (Site n W) (Site n W) R

/-- An `n × n` array of `W × W` blocks, the `(k, ℓ)` entry being
the block `H_{I_k I_ℓ}`. The outer indices are cyclic block labels. -/
abbrev BlockArray (n W : ℕ) (R : Type*) :=
  Matrix (ZMod n) (ZMod n) (Matrix (Fin W) (Fin W) R)

/-- The block decomposition `H ↦ (H_{I_k I_ℓ})_{k,ℓ}`,
with `(blockDecomp H k ℓ) a d = H_{(k,a),(ℓ,d)}` for all `k ℓ : ZMod n` and
`a d : Fin W` (zero-based internal labels). It is the inverse of Mathlib's
`Matrix.comp`, an exact reindexing with no normalization and no `NeZero`
hypothesis. -/
def blockDecomp : SiteMatrix n W R ≃ BlockArray n W R :=
  (Matrix.comp (ZMod n) (ZMod n) (Fin W) (Fin W) R).symm

/-- Entry formula for the `(k, ℓ)` block: `(H_{I_k I_ℓ})_{a d} = H_{(k,a),(ℓ,d)}`. -/
@[simp] theorem blockDecomp_apply (H : SiteMatrix n W R) (k l : ZMod n) (a d : Fin W) :
    blockDecomp H k l a d = H (k, a) (l, d) := rfl

/-- Block assembly: the site matrix of a block array `B` has entry
`B_{x.1, y.1}` at `(x.2, y.2)`. -/
@[simp] theorem blockDecomp_symm_apply (B : BlockArray n W R) (x y : Site n W) :
    blockDecomp.symm B x y = B x.1 y.1 x.2 y.2 := rfl

/-- The `(k, ℓ)` block is the submatrix of `H` along the block embeddings
`blockEmb k`, `blockEmb ℓ : Fin W ↪ Site n W`. -/
theorem blockDecomp_eq_submatrix (H : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp H k l = H.submatrix (blockEmb k) (blockEmb l) := rfl

/-- Two site matrices agree iff all their blocks agree. -/
theorem blockDecomp_ext {H H' : SiteMatrix n W R}
    (h : ∀ k l, blockDecomp H k l = blockDecomp H' k l) : H = H' :=
  blockDecomp.injective (funext fun k => funext fun l => h k l)

@[simp] theorem blockDecomp_zero [Zero R] (k l : ZMod n) :
    blockDecomp (0 : SiteMatrix n W R) k l = 0 := rfl

theorem blockDecomp_add [Add R] (A B : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp (A + B) k l = blockDecomp A k l + blockDecomp B k l := rfl

theorem blockDecomp_neg [Neg R] (A : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp (-A) k l = -blockDecomp A k l := rfl

theorem blockDecomp_sub [Sub R] (A B : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp (A - B) k l = blockDecomp A k l - blockDecomp B k l := rfl

theorem blockDecomp_smul {α : Type*} [SMul α R] (c : α) (A : SiteMatrix n W R)
    (k l : ZMod n) : blockDecomp (c • A) k l = c • blockDecomp A k l := rfl

/-- The identity on `R^{Λ_{n,W}}` has identity diagonal blocks and zero
off-diagonal blocks. -/
theorem blockDecomp_one [Zero R] [One R] (k l : ZMod n) :
    blockDecomp (1 : SiteMatrix n W R) k l = if k = l then 1 else 0 := by
  ext a d
  by_cases hkl : k = l
  · subst hkl
    by_cases had : a = d
    · subst had; simp
    · simp [one_apply, had]
  · simp [one_apply, hkl]

/-- Block multiplication: `(AB)_{I_k I_ℓ} = ∑_m A_{I_k I_m} B_{I_m I_ℓ}`, the sum
over all `n` block labels `m : ZMod n`. -/
theorem blockDecomp_mul [NeZero n] [NonUnitalNonAssocSemiring R]
    (A B : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp (A * B) k l = ∑ m, blockDecomp A k m * blockDecomp B m l := by
  ext a d
  simp [mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- `blockDecomp` as a ring isomorphism onto `n × n` block arrays with block
multiplication, the inverse of Mathlib's `Matrix.compRingEquiv`. -/
def blockDecompRingEquiv (n W : ℕ) (R : Type*) [NeZero n] [AddCommMonoid R] [Mul R] :
    SiteMatrix n W R ≃+* BlockArray n W R :=
  (Matrix.compRingEquiv (ZMod n) (Fin W) R).symm

@[simp] theorem coe_blockDecompRingEquiv [NeZero n] [AddCommMonoid R] [Mul R] :
    ⇑(blockDecompRingEquiv n W R) = blockDecomp := rfl

/-!
### Trace
-/

/-- Unnormalized trace: `Tr H = ∑_{k=0}^{n-1} Tr H_{I_k I_k}`.
Neither side is divided by a dimension. -/
theorem trace_block [NeZero n] [AddCommMonoid R] (H : SiteMatrix n W R) :
    H.trace = ∑ k, (blockDecomp H k k).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type]

/-- Unnormalized trace of a product in blocks:
`Tr (AB) = ∑_k ∑_ℓ Tr (A_{I_k I_ℓ} B_{I_ℓ I_k})`. -/
theorem trace_mul_block [NeZero n] [NonUnitalNonAssocSemiring R] (A B : SiteMatrix n W R) :
    (A * B).trace = ∑ k, ∑ l, (blockDecomp A k l * blockDecomp B l k).trace := by
  rw [trace_block]
  simp only [blockDecomp_mul, trace_sum]

/-!
### Adjoint and Hermitian structure
-/

/-- The `(k, ℓ)` block of the adjoint is the adjoint of the
`(ℓ, k)` block, `(H^*)_{I_k I_ℓ} = (H_{I_ℓ I_k})^*`, for all `k ℓ : ZMod n`. -/
theorem blockAdjoint [Star R] (H : SiteMatrix n W R) (k l : ZMod n) :
    blockDecomp Hᴴ k l = (blockDecomp H l k)ᴴ := rfl

/-- `H = H^*` iff `H_{I_ℓ I_k} = (H_{I_k I_ℓ})^*` for all block labels `k, ℓ`. -/
theorem isHermitian_iff_blockDecomp [Star R] (H : SiteMatrix n W R) :
    H.IsHermitian ↔ ∀ k l, blockDecomp H l k = (blockDecomp H k l)ᴴ := by
  constructor
  · intro h k l
    rw [← blockAdjoint, h.eq]
  · intro h
    exact blockDecomp_ext fun k l => (h l k).symm

/-- For Hermitian `H`, the diagonal block `H_{I_k I_k}` is Hermitian. -/
theorem IsHermitian.blockDecomp_diag [Star R] {H : SiteMatrix n W R} (hH : H.IsHermitian)
    (k : ZMod n) : (blockDecomp H k k).IsHermitian :=
  ((isHermitian_iff_blockDecomp H).1 hH k k).symm

/-- For Hermitian `H` the reverse bond
`H_{I_{k+1} I_k}` is the adjoint of the forward bond `H_{I_k I_{k+1}}`, with
`k + 1` read modulo `n`. -/
theorem IsHermitian.blockDecomp_reverse_bond [Star R] {H : SiteMatrix n W R}
    (hH : H.IsHermitian) (k : ZMod n) :
    blockDecomp H (k + 1) k = (blockDecomp H k (k + 1))ᴴ :=
  (isHermitian_iff_blockDecomp H).1 hH k (k + 1)

/-!
### Block-set restriction and the decomposition `S ⊕ R`
-/

/-- Sites whose block label lies in the set `S ⊆ ℤ/nℤ`, i.e. `⋃_{k ∈ S} I_k`. -/
abbrev BlockSetSite (S : Set (ZMod n)) (W : ℕ) := {x : Site n W // x.1 ∈ S}

/-- The block `H_{ST}` of `H` with rows in the blocks of `S`
and columns in the blocks of `T` (e.g. `H_{SS}`, `C = H_{RS}` with `R = Sᶜ`). -/
def restrictBlocks (S T : Set (ZMod n)) (H : SiteMatrix n W R) :
    Matrix (BlockSetSite S W) (BlockSetSite T W) R :=
  H.toBlock (fun x => x.1 ∈ S) (fun x => x.1 ∈ T)

@[simp] theorem restrictBlocks_apply (S T : Set (ZMod n)) (H : SiteMatrix n W R)
    (x : BlockSetSite S W) (y : BlockSetSite T W) :
    restrictBlocks S T H x y = H x.1 y.1 := rfl

/-- The decomposition `Λ = S ⊕ R` with `R = Sᶜ`, as an
equivalence from the disjoint union of the two block-set site types. -/
def splitEquiv (S : Set (ZMod n)) [DecidablePred (· ∈ S)] :
    BlockSetSite S W ⊕ BlockSetSite Sᶜ W ≃ Site n W :=
  Equiv.sumCompl fun x : Site n W => x.1 ∈ S

@[simp] theorem splitEquiv_inl (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (x : BlockSetSite S W) : splitEquiv S (Sum.inl x) = x.1 := rfl

@[simp] theorem splitEquiv_inr (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (x : BlockSetSite Sᶜ W) : splitEquiv S (Sum.inr x) = x.1 := rfl

/-- In the decomposition `S ⊕ R`,
`R = Sᶜ`, the matrix `H` is the block matrix
`[[H_{SS}, H_{SR}], [H_{RS}, H_{RR}]]`. -/
theorem submatrix_splitEquiv (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) :
    H.submatrix (splitEquiv S) (splitEquiv S) =
      fromBlocks (restrictBlocks S S H) (restrictBlocks S Sᶜ H)
        (restrictBlocks Sᶜ S H) (restrictBlocks Sᶜ Sᶜ H) := by
  ext (x | x) (y | y) <;> rfl

/-- Unnormalized trace splits over `S ⊕ R`: `Tr H = Tr H_{SS} + Tr H_{RR}`. -/
theorem trace_split [NeZero n] [AddCommMonoid R] (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) :
    H.trace = (restrictBlocks S S H).trace + (restrictBlocks Sᶜ Sᶜ H).trace := by
  simp only [Matrix.trace, Matrix.diag]
  rw [← (splitEquiv (W := W) S).sum_comp, Fintype.sum_sum_type]
  rfl

/-- The `(S, T)` block of the adjoint: `(H^*)_{ST} = (H_{TS})^*`. -/
theorem restrictBlocks_conjTranspose [Star R] (S T : Set (ZMod n)) (H : SiteMatrix n W R) :
    restrictBlocks S T Hᴴ = (restrictBlocks T S H)ᴴ := rfl

/-- For Hermitian `H`, every principal block `H_{SS}` is Hermitian. -/
theorem IsHermitian.restrictBlocks [Star R] {H : SiteMatrix n W R} (hH : H.IsHermitian)
    (S : Set (ZMod n)) : (BlockBand.restrictBlocks S S H).IsHermitian :=
  hH.submatrix _

/-- `H` is Hermitian iff `H_{SS}` and `H_{RR}` are Hermitian and the
coupling satisfies `H_{SR} = (H_{RS})^*` (`C^*` in the paper), `R = Sᶜ`. -/
theorem isHermitian_iff_split [InvolutiveStar R] (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) :
    H.IsHermitian ↔ (restrictBlocks S S H).IsHermitian ∧
      (restrictBlocks Sᶜ S H)ᴴ = restrictBlocks S Sᶜ H ∧
      (restrictBlocks Sᶜ Sᶜ H).IsHermitian := by
  rw [← isHermitian_submatrix_equiv (splitEquiv S), submatrix_splitEquiv,
    isHermitian_fromBlocks_iff]
  constructor
  · rintro ⟨h₁, -, h₃, h₄⟩
    exact ⟨h₁, h₃, h₄⟩
  · rintro ⟨h₁, h₃, h₄⟩
    refine ⟨h₁, ?_, h₃, h₄⟩
    rw [← h₃, conjTranspose_conjTranspose]

/-!
### Rank
-/

section Rank

variable [CommRing R] [StrongRankCondition R]

/-- Every block has rank at most that of `H`: `rank H_{I_k I_ℓ} ≤ rank H`. -/
theorem rank_blockDecomp_le [NeZero n] (H : SiteMatrix n W R) (k l : ZMod n) :
    (blockDecomp H k l).rank ≤ H.rank := by
  rw [blockDecomp_eq_submatrix]
  exact rank_submatrix_le H (fun a => (k, a)) (fun d => (l, d))

/-- A `W × W` block has rank at most `W`. -/
theorem rank_blockDecomp_le_width (H : SiteMatrix n W R) (k l : ZMod n) :
    (blockDecomp H k l).rank ≤ W := by
  simpa using rank_le_card_width (blockDecomp H k l)

/-- `rank H_{ST} ≤ rank H` for all sets of block labels `S, T`. -/
theorem rank_restrictBlocks_le [NeZero n] (S T : Set (ZMod n)) [DecidablePred (· ∈ T)]
    (H : SiteMatrix n W R) : (restrictBlocks S T H).rank ≤ H.rank :=
  rank_submatrix_le H Subtype.val Subtype.val

omit [StrongRankCondition R] in
/-- Writing `H` in the decomposition `S ⊕ R` preserves rank. -/
theorem rank_submatrix_splitEquiv [NeZero n] (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) : (H.submatrix (splitEquiv S) (splitEquiv S)).rank = H.rank :=
  rank_submatrix H _ _

omit [StrongRankCondition R] in
/-- `rank [[H_{SS}, H_{SR}], [H_{RS}, H_{RR}]] = rank H`, `R = Sᶜ`. -/
theorem rank_fromBlocks_split [NeZero n] (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) :
    (fromBlocks (restrictBlocks S S H) (restrictBlocks S Sᶜ H)
      (restrictBlocks Sᶜ S H) (restrictBlocks Sᶜ Sᶜ H)).rank = H.rank := by
  rw [← submatrix_splitEquiv, rank_submatrix_splitEquiv]

end Rank

/-!
### Positivity
-/

section Positivity

variable [Ring R] [PartialOrder R] [StarRing R]

/-- A positive semidefinite `H` has positive semidefinite diagonal blocks
`H_{I_k I_k}`. Over `ℂ` this uses `open scoped ComplexOrder`. -/
theorem PosSemidef.blockDecomp_diag {H : SiteMatrix n W R} (hH : H.PosSemidef)
    (k : ZMod n) : (blockDecomp H k k).PosSemidef :=
  hH.submatrix _

/-- A positive definite `H` has positive definite diagonal blocks `H_{I_k I_k}`. -/
theorem PosDef.blockDecomp_diag {H : SiteMatrix n W R} (hH : H.PosDef)
    (k : ZMod n) : (blockDecomp H k k).PosDef :=
  hH.submatrix (blockEmb k).injective

/-- `Tr H_{I_k I_k} ≥ 0` for positive semidefinite `H` (unnormalized trace). -/
theorem PosSemidef.trace_blockDecomp_diag_nonneg [AddLeftMono R]
    {H : SiteMatrix n W R} (hH : H.PosSemidef) (k : ZMod n) :
    0 ≤ (blockDecomp H k k).trace :=
  (PosSemidef.blockDecomp_diag hH k).trace_nonneg

/-- A positive semidefinite `H` has positive semidefinite principal blocks `H_{SS}`. -/
theorem PosSemidef.restrictBlocks {H : SiteMatrix n W R} (hH : H.PosSemidef)
    (S : Set (ZMod n)) :
    (BlockBand.restrictBlocks S S H).PosSemidef :=
  hH.submatrix _

/-- A positive definite `H` has positive definite principal blocks `H_{SS}`. -/
theorem PosDef.restrictBlocks {H : SiteMatrix n W R} (hH : H.PosDef)
    (S : Set (ZMod n)) :
    (BlockBand.restrictBlocks S S H).PosDef :=
  hH.submatrix Subtype.val_injective

/-- `H ⪰ 0` iff its block form in the decomposition `S ⊕ R`, `R = Sᶜ`, is
positive semidefinite. -/
theorem posSemidef_iff_split (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (H : SiteMatrix n W R) :
    H.PosSemidef ↔ (fromBlocks (restrictBlocks S S H) (restrictBlocks S Sᶜ H)
      (restrictBlocks Sᶜ S H) (restrictBlocks Sᶜ Sᶜ H)).PosSemidef := by
  rw [← submatrix_splitEquiv, posSemidef_submatrix_equiv]

end Positivity

/-!
### Relation to the block projections `P_k`
-/

/-- Compressing by the block projections,
`(P_k H P_ℓ)_{xy} = H_{xy}` if `x ∈ I_k` and `y ∈ I_ℓ`, and `0` otherwise; i.e.
`P_k H P_ℓ` is the block `H_{I_k I_ℓ}` extended by zero. -/
theorem blockProj_mul_mul_blockProj_apply [NeZero n] (H : SiteMatrix n W ℂ)
    (k l : ZMod n) (x y : Site n W) :
    (blockProj k * H * blockProj l : SiteMatrix n W ℂ) x y =
      if x.1 = k ∧ y.1 = l then H x y else 0 := by
  simp only [blockProj, diagonal_mul, mul_diagonal]
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = l <;> simp [hx, hy]

end CoareaNative.BlockBand
