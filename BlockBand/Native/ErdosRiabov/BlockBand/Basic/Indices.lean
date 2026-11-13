module

public import BlockBand.Native.ErdosRiabov.BlockBand.Basic.Parameters
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
* Cyclic adjacency is `ℓ = k + 1 ∨ ℓ = k - 1` in `ZMod n`, i.e. the model's
  "indices read modulo `n`".

Every statement needing a finite cyclic domain takes an explicit `[NeZero n]`
argument. No global `NeZero` instance is declared; `Params.neZero_n` is a
theorem to be installed locally with `haveI`.

Not treated here: eigenvector masses `p_{αk}`, mass profiles `ν_α`, the Gaussian matrix law,
probability, QUE, and limits.
-/

@[expose] public section

set_option autoImplicit false

namespace ERNative.BlockBand

open Matrix

/-!
### Sites and the flattening
-/

/-- The site set `Λ_{n,W} = (ℤ/nℤ) × {1,…,W}`, definitionally
`Conventions.Site n W = ZMod n × Fin W`. The zero-based internal coordinate `a₀ : Fin W`
stands for the label `a = a₀ + 1` of the paper. No parity or size condition on `n` is imposed
at the type level.
-/
abbrev Site (n W : ℕ) := Conventions.Site n W

/-- The row-major flattening `Conventions.siteEquivFin`, re-exported without change:
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

/-- The finite block `I_k`, for a nonzero modulus. -/
def blockFinset (n W : ℕ) [NeZero n] (k : ZMod n) : Finset (Site n W) :=
  Finset.univ.map (blockEmb k)

@[simp] theorem mem_blockFinset {n W : ℕ} [NeZero n] {k : ZMod n} {x : Site n W} :
    x ∈ blockFinset n W k ↔ x.1 = k := by
  simp only [blockFinset, Finset.mem_map, Finset.mem_univ, true_and, blockEmb_apply]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ rfl, fun hx => ⟨x.2, Prod.ext hx.symm rfl⟩⟩

/-- Every block has exactly `W` sites, `|I_k| = W`. -/
@[simp] theorem card_blockFinset (n W : ℕ) [NeZero n] (k : ZMod n) :
    (blockFinset n W k).card = W := by
  simp [blockFinset]

/-!
### Block projections
-/

/-- The orthogonal projection `P_k` of
`ℂ^{Λ_{n,W}}` onto `ℂ^{I_k}`, written in site coordinates as the diagonal
`0/1` matrix with entry `1` exactly at sites of block `k`. -/
def blockProj {n W : ℕ} (k : ZMod n) : Matrix (Site n W) (Site n W) ℂ :=
  Matrix.diagonal fun x => if x.1 = k then 1 else 0

/-- Projection law: `P_k² = P_k`. -/
@[simp] theorem blockProj_mul_self {n W : ℕ} [NeZero n] (k : ZMod n) :
    blockProj (W := W) k * blockProj k = blockProj k := by
  rw [blockProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

/-- `P_k` is self-adjoint: `P_k^* = P_k`. -/
@[simp] theorem blockProj_conjTranspose {n W : ℕ} (k : ZMod n) :
    (blockProj (W := W) k)ᴴ = blockProj k := by
  rw [blockProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  split_ifs <;> simp_all

/-!
### Cyclic adjacency
-/

/-- Block labels `k, ℓ` are bond-adjacent when `ℓ = k + 1` or
`ℓ = k - 1` in `ZMod n` ("the indices are read modulo `n`"). For `n ≥ 3` the
two neighbours are distinct and differ from `k`. -/
def IsAdjacent {n : ℕ} (k l : ZMod n) : Prop := l = k + 1 ∨ l = k - 1

/-- Adjacency is symmetric. -/
theorem IsAdjacent.symm {n : ℕ} {k l : ZMod n} (h : IsAdjacent k l) : IsAdjacent l k := by
  rcases h with rfl | rfl
  · right; ring
  · left; ring

private theorem natCast_ne_zero_of_lt {n m : ℕ} (hm : 0 < m) (h : m < n) :
    (m : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hd => absurd (Nat.le_of_dvd hm hd) (Nat.not_le.2 h)

/-- For `n ≥ 3` (in particular for every admissible `n ≥ 4`), the two cyclic
neighbours of a block are distinct, so each block has exactly two bonds. -/
theorem add_one_ne_sub_one {n : ℕ} (hn : 3 ≤ n) (k : ZMod n) : k + 1 ≠ k - 1 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by
    have h' := congrArg (· - (k - 1)) h
    simp only [sub_self] at h'
    rw [← h']; push_cast; ring
  exact natCast_ne_zero_of_lt two_pos hn this

/-!
### Parameter bridge
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

end Params

end ERNative.BlockBand
