module

public import BlockBand.Palm.MomentFlow.Steps2Duhamel
public import BlockBand.Palm.MomentFlow.Steps2Gap
public import BlockBand.Palm.MomentFlow.FlowRates

/-!
# Duhamel tails are forward short-flow solutions

`tail_eq_forward`: the Duhamel tail integrand at time `v` is the forward solution started at time
`v` from the indicator of `sector \ W`, evaluated at `(u, ξ)`.
-/

set_option autoImplicit false

@[expose] public section

open Set Finset BlockBand.Internal.Contracts.CoareaPalm

namespace BlockBand.Palm.MomentFlow

variable {N : ℕ}

/-- The Duhamel tail integrand at time `v` is the forward solution started at time `v` from the
indicator of `sector \ W`, evaluated at `(u, ξ)`. -/
theorem tail_eq_forward {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u v : ℝ}
    (hsym : ∀ x ∈ Ioo s u, ∀ i j, c x i j = c x j i) {w Φ : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) (hv : v ∈ Icc s u) (W : Finset (Occ N))
    (hΦ : IsMomentFlowSolution c r v u Φ)
    (hΦ0 : ∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ W then 0 else 1) :
    ∑ ζ ∈ sector N r \ W, w v ζ = Φ u ξ := by
  classical
  have h := (hw.mono hv.1).represent hv.2
    (fun x hx => hsym x ⟨lt_of_le_of_lt hv.1 hx.1, hx.2⟩) hΦ
  have hR : ∑ ζ ∈ sector N r, w u ζ * Φ u ζ = Φ u ξ := by
    rw [Finset.sum_congr rfl fun ζ hζ => by rw [hwu ζ hζ]]
    exact sum_deltaCfg_mul hξ _
  have hL : ∑ ζ ∈ sector N r, w v ζ * Φ v ζ = ∑ ζ ∈ sector N r \ W, w v ζ := by
    have hsd : sector N r \ W = (sector N r).filter (fun ζ => ζ ∉ W) := by
      ext ζ; simp [Finset.mem_sdiff]
    rw [Finset.sum_congr rfl fun ζ hζ => by rw [hΦ0 ζ hζ], hsd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    split_ifs <;> simp_all
  rw [← hL, h, hR]

end BlockBand.Palm.MomentFlow
