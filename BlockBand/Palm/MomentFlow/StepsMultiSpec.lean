module

public import BlockBand.Palm.MomentFlow.FlowRates
public import Mathlib.Data.List.Sort

/-!
# The `r`-particle short finite-speed statement

* `occLabels ξ`: the sorted list of particle labels of `ξ` (with multiplicity).
* `occDist ξ ζ`: the ordered matching distance `∑_k |x_k - y_k|` between the sorted label lists
  (the ordered matching distance); for `ξ, ζ` in the same sector the lists have equal length.
* `MultiShortFiniteSpeed`: moment-flow scales of `short_row` (`θ = 1/100`, `τ = N^{-θ}`,
  `a = c - τ`, `ℓ = ⌊N^{1-θ/3}⌋`, `R = N^ε ℓ`); fixed constants and `A` first; for every `r ≥ 1`
  and `ε > 0` a `c' > 0`; for every `D` an `N₀`; for `N ≥ N₀`, `F` in the fresh class, every
  deterministic `a ≤ s ≤ u ≤ c` and `ξ` in the `r`-sector: outside `flowLaw N a`-probability
  `N^{-D}`, if every particle of `ξ` has bulk position at time `s` (`|λ_k(s) - E| ≤ r₀/16`), then
  every solution `Φ` on `[s,u]` of the short moment flow (`IsMomentFlowSolution` for
  `shortFlowRate F a ω ℓ`) started from the indicator of `{ζ : occDist ξ ζ > rR}` has
  `Φ(u, ξ) ≤ exp(-c' N^ε)`. This is the row form; for `r = 1` it is `short_row`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Sorted particle labels of a configuration (with multiplicity), as naturals. -/
def occLabels (ξ : Occ N) : List ℕ :=
  ((Finset.univ : Finset (Fin N)).val.bind (fun i => Multiset.replicate (ξ i) (i : ℕ))).sort (· ≤ ·)

/-- Ordered matching distance between configurations. -/
def occDist (ξ ζ : Occ N) : ℕ :=
  ((occLabels ξ).zip (occLabels ζ)).foldr (fun p acc => Int.natAbs ((p.1 : ℤ) - p.2) + acc) 0

/-- **The `r`-particle short finite-speed statement** (row form). -/
def MultiShortFiniteSpeed : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ ξ ∈ sector N r,
        flowLaw N a {ω | (∀ k : Fin N, 0 < ξ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
          ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
            (∀ ζ ∈ sector N r, Φ s ζ = if (r : ℝ) * R < (occDist ξ ζ : ℝ) then 1 else 0) ∧
            Real.exp (-(c' * (N : ℝ) ^ ε)) < Φ u ξ} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

end BlockBand.Palm.MomentFlow
