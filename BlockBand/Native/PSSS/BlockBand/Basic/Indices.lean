module

public import BlockBand.Native.PSSS.BlockBand.Basic.Parameters
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

namespace PSSSNative.BlockBand

open Matrix

/-!
### Sites and the flattening
-/

/-!
### Terminal labels
-/

/-!
### Blocks
-/

/-!
### Block projections
-/

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

/-!
### Parameter bridge
-/

namespace Params

/-- The block count of admissible parameters is nonzero. This is a
theorem, **not** a global instance; install it locally with `haveI`. -/
theorem neZero_n (p : Params) : NeZero p.n := ⟨p.n_ne_zero⟩

end Params

end PSSSNative.BlockBand
