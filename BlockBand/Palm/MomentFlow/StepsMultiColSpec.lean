module

public import BlockBand.Palm.MomentFlow.StepsMultiSpec

/-!
# The `r`-particle short finite-speed statement, column form

`MultiShortColumnSpeed`: at the moment-flow scales (`τ = N^{-1/100}`, `a = c - τ`,
`ℓ = ⌊N^{1-1/300}⌋`, `R = N^ε ℓ`), outside `flowLaw N a`-probability `N^{-D}`, if every particle
of `ξ` is in the bulk at time `s`, every short moment-flow solution on `[s,u]` started from `δ_ξ`
has mass at most `exp(-c' N^ε)` at time `u` on `{ζ : occDist ξ ζ > rR}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open BlockBand.Internal.Contracts.CoareaPalm

/-- **The `r`-particle short finite-speed input, column form.** -/
def MultiShortColumnSpeed : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ ξ ∈ sector N r,
        flowLaw N a {ω | (∀ k : Fin N, 0 < ξ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
          ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
            (∀ ζ ∈ sector N r, Φ s ζ = if ζ = ξ then 1 else 0) ∧
            Real.exp (-(c' * (N : ℝ) ^ ε)) <
              ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ ζ : ℝ)), Φ u ζ} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

end BlockBand.Palm.MomentFlow
