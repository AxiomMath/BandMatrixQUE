module

public import BlockBand.Coarea.Native.BlockBand.Basic.Parameters
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

/-!
# Sites, blocks, block projections, and cyclic adjacency

* The only flattening is the row-major `Conventions.siteEquivFin`,
  `(k, a₀) ↦ a₀ + W k₀`; it is re-exported here, never re-implemented.
* `block n W k` is the set `I_k`, `blockEmb k` its parametrisation by `Fin W`,
  and `blockProj k` the coordinate (diagonal `0/1`) matrix of `P_k` on
  `ℂ^{Λ_{n,W}}`.
* Cyclic adjacency is `ℓ = k + 1 ∨ ℓ = k - 1` in `ZMod n`, i.e. the paper's
  "indices read modulo `n`" in the definition of the model.

Every statement needing a finite cyclic domain takes an explicit `[NeZero n]`
argument. No global `NeZero` instance is declared; `Params.neZero_n` is a
theorem to be installed locally with `haveI`.
-/

@[expose] public section

set_option autoImplicit false

namespace CoareaNative.BlockBand

open Matrix

/-!
### Sites and the row-major flattening
-/

/-- The site set `Λ_{n,W} = (ℤ/nℤ) × {1,…,W}`, definitionally
`Conventions.Site n W = ZMod n × Fin W`.  The zero-based coordinate `a₀ : Fin W`
stands for the label `a = a₀ + 1`.  No parity or size condition on `n` is imposed
at the type level. -/
abbrev Site (n W : ℕ) := Conventions.Site n W

/-- The row-major flattening, re-exported without change:
for `[NeZero n]`, `(k, a₀) ↦ a₀ + W k₀` with `k₀ = k.val ∈ [0, n)`. -/
abbrev siteEquivFin (n W : ℕ) [NeZero n] : Site n W ≃ Fin (Conventions.dimension n W) :=
  Conventions.siteEquivFin n W

/-- The zero-based flat index of a site is `a₀ + W k₀`. -/
@[simp] theorem siteEquivFin_val (n W : ℕ) [NeZero n] (x : Site n W) :
    (siteEquivFin n W x).val = x.2.val + W * x.1.val :=
  Conventions.siteEquivFin_apply_val n W x

/-- `|Λ_{n,W}| = L = nW` for every `n ≠ 0` and every `W`. -/
theorem card_site (n W : ℕ) [NeZero n] :
    Fintype.card (Site n W) = Conventions.dimension n W := by
  simp [Site, Conventions.Site, Conventions.dimension, ZMod.card]

/-!
### Terminal labels
-/

/-- at width `W + 1`, the last zero-based internal coordinate
`Fin.last W` has one-based label `W + 1`, the terminal element of `{1,…,W+1}`. -/
theorem sourceInternalLabel_last (W : ℕ) :
    Conventions.sourceInternalLabel (Fin.last W) = W + 1 := rfl

/-- For `W ≥ 1`, the terminal internal coordinate `⟨W - 1, _⟩`
has one-based label exactly `W`. -/
theorem sourceInternalLabel_terminal {W : ℕ} (hW : 0 < W) :
    Conventions.sourceInternalLabel (⟨W - 1, Nat.sub_lt hW Nat.one_pos⟩ : Fin W) = W := by
  simp [Conventions.sourceInternalLabel]
  omega

/-- The terminal site `(n - 1, W - 1)` is flattened to the last
zero-based index `nW - 1`; equivalently its one-based site rank is `L = nW`. -/
theorem siteEquivFin_terminal_val (n W : ℕ) [NeZero n] (hW : 0 < W) :
    (siteEquivFin n W (((n - 1 : ℕ) : ZMod n),
      (⟨W - 1, Nat.sub_lt hW Nat.one_pos⟩ : Fin W))).val =
      Conventions.dimension n W - 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [siteEquivFin_val]
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.sub_lt hn Nat.one_pos),
    Conventions.dimension]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.add_mul, Nat.mul_add]
  ring_nf
  omega

/-!
### Blocks
-/

/-- The `k`-th block `I_k = {k} × {1,…,W}` as a set of sites. -/
def block (n W : ℕ) (k : ZMod n) : Set (Site n W) := {x | x.1 = k}

/-- Membership in `I_k` is equality of the cyclic block label. -/
@[simp] theorem mem_block {n W : ℕ} {k : ZMod n} {x : Site n W} :
    x ∈ block n W k ↔ x.1 = k := Iff.rfl

/-- The embedding `a₀ ↦ (k, a₀)` of the internal coordinates
into the `k`-th block. -/
def blockEmb {n W : ℕ} (k : ZMod n) : Fin W ↪ Site n W :=
  ⟨fun a => (k, a), fun _ _ h => (Prod.mk.inj h).2⟩

@[simp] theorem blockEmb_apply {n W : ℕ} (k : ZMod n) (a : Fin W) :
    blockEmb k a = (k, a) := rfl

/-- The image of the block embedding is exactly `I_k`. -/
theorem range_blockEmb {n W : ℕ} (k : ZMod n) :
    Set.range (blockEmb (W := W) k) = block n W k := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro hx; exact ⟨x.2, Prod.ext hx.symm rfl⟩

/-- The flat index of `(k, a₀) ∈ I_k` is `a₀ + W k₀`, so block
`k` occupies the contiguous zero-based range `[W k₀, W k₀ + W)`. -/
theorem siteEquivFin_blockEmb_val (n W : ℕ) [NeZero n] (k : ZMod n) (a : Fin W) :
    (siteEquivFin n W (blockEmb k a)).val = a.val + W * k.val :=
  siteEquivFin_val n W (k, a)

/-- Distinct block labels give disjoint blocks. -/
theorem block_disjoint {n W : ℕ} {k l : ZMod n} (h : k ≠ l) :
    Disjoint (block n W k) (block n W l) :=
  Set.disjoint_left.2 fun _ hk hl => h (hk.symm.trans hl)

/-- The blocks cover the site set. -/
theorem iUnion_block (n W : ℕ) : ⋃ k, block n W k = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x.1, rfl⟩

/-- The finite block `I_k`, for a nonzero modulus. -/
def blockFinset (n W : ℕ) [NeZero n] (k : ZMod n) : Finset (Site n W) :=
  Finset.univ.map (blockEmb k)

@[simp] theorem mem_blockFinset {n W : ℕ} [NeZero n] {k : ZMod n} {x : Site n W} :
    x ∈ blockFinset n W k ↔ x.1 = k := by
  simp only [blockFinset, Finset.mem_map, Finset.mem_univ, true_and, blockEmb_apply]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ rfl, fun hx => ⟨x.2, Prod.ext hx.symm rfl⟩⟩

theorem coe_blockFinset (n W : ℕ) [NeZero n] (k : ZMod n) :
    (blockFinset n W k : Set (Site n W)) = block n W k := by
  ext x; simp

/-- Every block has exactly `W` sites, `|I_k| = W`. -/
@[simp] theorem card_blockFinset (n W : ℕ) [NeZero n] (k : ZMod n) :
    (blockFinset n W k).card = W := by
  simp [blockFinset]

/-- `|I_k| = W`, stated for the set-valued block. -/
theorem ncard_block (n W : ℕ) [NeZero n] (k : ZMod n) :
    (block n W k).ncard = W := by
  rw [← coe_blockFinset, Set.ncard_coe_finset, card_blockFinset]

/-!
### Block projections
-/

/-- The orthogonal projection `P_k` of
`ℂ^{Λ_{n,W}}` onto `ℂ^{I_k}`, written in site coordinates as the diagonal
`0/1` matrix with entry `1` exactly at sites of block `k`. -/
def blockProj {n W : ℕ} (k : ZMod n) : Matrix (Site n W) (Site n W) ℂ :=
  Matrix.diagonal fun x => if x.1 = k then 1 else 0

theorem blockProj_apply {n W : ℕ} (k : ZMod n) (x y : Site n W) :
    blockProj k x y = if x = y ∧ x.1 = k then 1 else 0 := by
  by_cases hxy : x = y
  · subst hxy; simp [blockProj]
  · simp [blockProj, hxy]

/-- `P_k` acts on a vector by restricting it to `I_k` (and zero elsewhere). -/
theorem blockProj_mulVec {n W : ℕ} [NeZero n] (k : ZMod n) (v : Site n W → ℂ)
    (x : Site n W) :
    (blockProj k *ᵥ v) x = if x.1 = k then v x else 0 := by
  simp [blockProj, Matrix.mulVec_diagonal]

/-- Projection law: `P_k² = P_k`. -/
@[simp] theorem blockProj_mul_self {n W : ℕ} [NeZero n] (k : ZMod n) :
    blockProj (W := W) k * blockProj k = blockProj k := by
  rw [blockProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

/-- Orthogonality: `P_k P_ℓ = 0` for distinct block labels. -/
theorem blockProj_mul_of_ne {n W : ℕ} [NeZero n] {k l : ZMod n} (h : k ≠ l) :
    blockProj (W := W) k * blockProj l = 0 := by
  rw [blockProj, blockProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext x
  by_cases hk : x.1 = k
  · have hl : x.1 ≠ l := fun hl => h (hk.symm.trans hl)
    simp [hl]
  · simp [hk]

/-- `P_k` is self-adjoint: `P_k^* = P_k`. -/
@[simp] theorem blockProj_conjTranspose {n W : ℕ} (k : ZMod n) :
    (blockProj (W := W) k)ᴴ = blockProj k := by
  rw [blockProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  split_ifs <;> simp_all

theorem blockProj_isHermitian {n W : ℕ} (k : ZMod n) :
    (blockProj (W := W) k).IsHermitian :=
  blockProj_conjTranspose k

/-- Resolution of the identity: `∑_{k=0}^{n-1} P_k = 1` on `ℂ^{Λ_{n,W}}`,
the coordinate form of `∑_k p_{αk} = 1`. -/
theorem sum_blockProj (n W : ℕ) [NeZero n] :
    ∑ k : ZMod n, blockProj (W := W) k = 1 := by
  ext x y
  simp only [Matrix.sum_apply, blockProj_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

/-- `rank P_k = tr P_k = W = |I_k|`. -/
theorem trace_blockProj (n W : ℕ) [NeZero n] (k : ZMod n) :
    (blockProj (W := W) k).trace = W := by
  rw [blockProj, Matrix.trace_diagonal, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.univ.filter fun x : Site n W => x.1 = k) = blockFinset n W k := by
    ext x; simp
  rw [this, card_blockFinset]

/-!
### Cyclic adjacency
-/

/-- Block labels `k, ℓ` are bond-adjacent when `ℓ = k + 1` or
`ℓ = k - 1` in `ZMod n` ("the indices are read modulo `n`"). For `n ≥ 3` the
two neighbours are distinct and differ from `k`. -/
def IsAdjacent {n : ℕ} (k l : ZMod n) : Prop := l = k + 1 ∨ l = k - 1

instance {n : ℕ} (k l : ZMod n) : Decidable (IsAdjacent k l) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Adjacency is symmetric. -/
theorem IsAdjacent.symm {n : ℕ} {k l : ZMod n} (h : IsAdjacent k l) : IsAdjacent l k := by
  rcases h with rfl | rfl
  · right; ring
  · left; ring

theorem isAdjacent_comm {n : ℕ} (k l : ZMod n) : IsAdjacent k l ↔ IsAdjacent l k :=
  ⟨IsAdjacent.symm, IsAdjacent.symm⟩

theorem isAdjacent_add_one {n : ℕ} (k : ZMod n) : IsAdjacent k (k + 1) := Or.inl rfl

theorem isAdjacent_sub_one {n : ℕ} (k : ZMod n) : IsAdjacent k (k - 1) := Or.inr rfl

/-- Forward wrap: the last block label `n - 1` is followed by `0`. -/
theorem last_add_one (n : ℕ) [NeZero n] : (((n - 1 : ℕ) : ZMod n) + 1) = 0 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have h : (((n - 1 : ℕ) : ZMod n) + 1) = ((n - 1 + 1 : ℕ) : ZMod n) := by push_cast; ring
  rw [h, Nat.sub_add_cancel hn, ZMod.natCast_self]

/-- Backward wrap: the predecessor of `0` is the last block label `n - 1`. -/
theorem zero_sub_one (n : ℕ) [NeZero n] : (0 : ZMod n) - 1 = ((n - 1 : ℕ) : ZMod n) := by
  rw [← last_add_one n]; ring

/-- `0` and `n - 1` are adjacent across the wrap. -/
theorem isAdjacent_last_zero (n : ℕ) [NeZero n] :
    IsAdjacent ((n - 1 : ℕ) : ZMod n) 0 :=
  Or.inl (last_add_one n).symm

/-- Representative form of the forward neighbour: `(k + 1).val = (k.val + 1) % n`. -/
theorem val_add_one (n : ℕ) [NeZero n] (k : ZMod n) :
    (k + 1).val = (k.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have : n = 1 := le_antisymm h (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
    subst this; simp [Nat.mod_one]

private theorem natCast_ne_zero_of_lt {n m : ℕ} (hm : 0 < m) (h : m < n) :
    (m : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hd => absurd (Nat.le_of_dvd hm hd) (Nat.not_le.2 h)

/-- For `n ≥ 2`, the forward neighbour differs from `k`. -/
theorem add_one_ne_self {n : ℕ} (hn : 2 ≤ n) (k : ZMod n) : k + 1 ≠ k := by
  intro h
  have : ((1 : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_one]; simpa using congrArg (· - k) h
  exact natCast_ne_zero_of_lt Nat.one_pos hn this

/-- For `n ≥ 2`, the backward neighbour differs from `k`. -/
theorem sub_one_ne_self {n : ℕ} (hn : 2 ≤ n) (k : ZMod n) : k - 1 ≠ k := by
  intro h
  apply add_one_ne_self hn (k - 1)
  rw [sub_add_cancel, h]

/-- For `n ≥ 3` (in particular for every admissible `n ≥ 4`), the two cyclic
neighbours of a block are distinct, so each block has exactly two bonds. -/
theorem add_one_ne_sub_one {n : ℕ} (hn : 3 ≤ n) (k : ZMod n) : k + 1 ≠ k - 1 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by
    have h' := congrArg (· - (k - 1)) h
    simp only [sub_self] at h'
    rw [← h']; push_cast; ring
  exact natCast_ne_zero_of_lt two_pos hn this

/-- Adjacency is irreflexive once `n ≥ 2`. -/
theorem not_isAdjacent_self {n : ℕ} (hn : 2 ≤ n) (k : ZMod n) : ¬ IsAdjacent k k := by
  rintro (h | h)
  · exact add_one_ne_self hn k h.symm
  · exact sub_one_ne_self hn k h.symm

/-- The paper's block projections are mutually orthogonal idempotents,
resolve the identity, and each have unnormalized trace `W`. -/
theorem blockProj_resolution (n W : ℕ) [NeZero n] :
    (∀ k : ZMod n, blockProj (W := W) k * blockProj k = blockProj k) ∧
    (∀ k l : ZMod n, k ≠ l → blockProj (W := W) k * blockProj l = 0) ∧
    (∑ k : ZMod n, blockProj (W := W) k = 1) ∧
    (∀ k : ZMod n, (blockProj (W := W) k).trace = W) := by
  refine ⟨blockProj_mul_self, ?_, sum_blockProj n W, trace_blockProj n W⟩
  intro k l hkl
  exact blockProj_mul_of_ne hkl

/-!
### Parameters
-/

namespace Params

/-- The block count of admissible parameters is nonzero. This is a
theorem, **not** a global instance; install it locally with `haveI`. -/
theorem neZero_n (p : Params) : NeZero p.n := ⟨p.n_ne_zero⟩

/-- For admissible parameters `|Λ_{n,W}| = L`. -/
theorem card_site (p : Params) :
    haveI := p.neZero_n
    Fintype.card (Site p.n p.W) = p.L := by
  have := p.neZero_n
  exact BlockBand.card_site p.n p.W

/-- Since `n ≥ 4`, the two neighbours of every block are distinct. -/
theorem add_one_ne_sub_one (p : Params) (k : ZMod p.n) : k + 1 ≠ k - 1 :=
  BlockBand.add_one_ne_sub_one (le_trans (by norm_num) p.n_ge_four) k

/-- The parameter-level site equivalence is the re-exported flattening. -/
theorem siteIndexEquiv_eq (p : Params) :
    haveI := p.neZero_n
    p.siteIndexEquiv = siteEquivFin p.n p.W := rfl

end Params

end CoareaNative.BlockBand
