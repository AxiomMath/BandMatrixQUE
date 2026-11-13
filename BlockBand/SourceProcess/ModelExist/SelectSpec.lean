module

public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# The perpendicular-birth selection: specification

For a Gram state `H = (M, B)` of the extended frame (columns `c'`), the current columns `cur`
and earlier birth vectors `prev`, a birth vector `a` of squared norm `v` must satisfy
(`SelSpec`): `(M − B)a = 0` (the new column `X a` is near), `(Ma)_k = 0` for current `k` and
`prev_lᴴ M a = 0` (it is perpendicular to the current columns and to the earlier probes), and
`aᴴ M a = v`. `SelExists`: some `w` satisfies the linear conditions with `M w ≠ 0`.
`PerpSelection`: a Borel-measurable choice satisfying `SelSpec` wherever `SelExists` holds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] {n : ℕ}

/-- The linear conditions on a birth vector. -/
def SelLin (cur : c' → Prop) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ)
    (a : c' → ℂ) : Prop :=
  (H.1 - H.2) *ᵥ a = 0 ∧ (∀ k, cur k → (H.1 *ᵥ a) k = 0) ∧
    ∀ l, star (prev l) ⬝ᵥ (H.1 *ᵥ a) = 0

/-- The specification of a birth vector of squared norm `v`. -/
def SelSpec (cur : c' → Prop) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ)
    (v : ℝ) (a : c' → ℂ) : Prop :=
  SelLin cur H prev a ∧ star a ⬝ᵥ (H.1 *ᵥ a) = (v : ℂ)

/-- A direction satisfying the linear conditions exists. -/
def SelExists (cur : c' → Prop) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) :
    Prop :=
  ∃ w, SelLin cur H prev w ∧ H.1 *ᵥ w ≠ 0

variable (c' n) in
/-- **A measurable perpendicular selection** for Gram states with `M ⪰ 0`, `M − B ⪰ 0`. -/
def PerpSelection (cur : c' → Prop) : Prop :=
  ∃ sel : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ → c' → ℂ, Measurable sel ∧
    ∀ (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) (v : ℝ), 0 ≤ v →
      H.1.PosSemidef → (H.1 - H.2).PosSemidef → SelExists cur H prev →
        SelSpec cur H prev v (sel (H, prev, v))

end BlockBand.SourceProcess.ModelExist
