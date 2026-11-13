module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Parameters
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Prod
public import Lean.Elab.Tactic.Omega
public import Mathlib

/-!
# Sites, blocks, and cyclic adjacency

* The only flattening is the row-major `Conventions.siteEquivFin`,
  `(k, a₀) ↦ a₀ + W k₀`; it is re-exported here, never re-implemented.
* `block n W k` is the set `I_k` of sites in block `k`.
* Cyclic adjacency is `ℓ = k + 1 ∨ ℓ = k - 1` in `ZMod n`, i.e. the paper's
  "indices read modulo `n`" in the definition of the model.

Every statement needing a finite cyclic domain takes an explicit `[NeZero n]`
argument. No global `NeZero` instance is declared; `Params.neZero_n` is a
theorem to be installed locally with `haveI`.
-/

@[expose] public section

set_option autoImplicit false

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel

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
### Blocks
-/

/-- The `k`-th block `I_k = {k} × {1,…,W}` as a set of sites. -/
def block (n W : ℕ) (k : ZMod n) : Set (Site n W) := {x | x.1 = k}

/-- Membership in `I_k` is equality of the cyclic block label. -/
@[simp] theorem mem_block {n W : ℕ} {k : ZMod n} {x : Site n W} :
    x ∈ block n W k ↔ x.1 = k := Iff.rfl

/-!
### Cyclic adjacency
-/

/-- Block labels `k, ℓ` are bond-adjacent when `ℓ = k + 1` or
`ℓ = k - 1` in `ZMod n` ("the indices are read modulo `n`"). For `n ≥ 3` the
two neighbours are distinct and differ from `k`. -/
def IsAdjacent {n : ℕ} (k l : ZMod n) : Prop := l = k + 1 ∨ l = k - 1

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
  exact BlockBand.Adapters.ErdosRiabov.CyclicModel.card_site p.n p.W

end Params

end BlockBand.Adapters.ErdosRiabov.CyclicModel
