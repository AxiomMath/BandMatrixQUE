module

public import BlockBand.Palm.MomentFlow.FlowRates

/-!
# Finite speed for `r = 1`: the short moment flow inherits `short_row`

* `shortRow_of_momentFlow`: on the moment-flow scales of `short_row`, for deterministic
  `a ≤ s ≤ u ≤ c` and a label `k`, outside `flowLaw N a`-probability `N^{-D}`: if `λ_k(s)` is in the
  bulk, every one-particle short moment-flow solution `Φ` on `[s,u]` started from
  `Φ(s, δ_j) = 1{|j - k| > R}` has `Φ(u, δ_k) ≤ exp(-c' N^ε)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- **Finite speed for `r = 1`** (from `RelativeLocalizationContract`). -/
theorem shortRow_of_momentFlow (hRL : RelativeLocalizationContract) (A c r₀ s₀ v₀ : ℝ)
    (hK : FreshConstants c r₀ s₀ v₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        let R : ℝ := (N : ℝ) ^ ε * ℓ
        ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
          flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) 1 s u Φ ∧
              (∀ j : Fin N, Φ s (Pi.single j 1) = if R < (labelDist k j : ℝ) then 1 else 0) ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) < Φ u (Pi.single k 1)} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  obtain ⟨c', hc', hD⟩ := hRL.short_row A c r₀ s₀ v₀ hK ε hε
  refine ⟨c', hc', fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hD D
  refine ⟨N₀, fun N hN F E hC => ?_⟩
  intro a ℓ R s u has hsu huc k
  refine le_trans (measure_mono ?_) (hN₀ N hN F E hC s u has hsu huc k)
  rintro ω ⟨hbulk, Φ, hΦ, hinit, hbig⟩
  refine ⟨hbulk, fun x k => Φ x (Pi.single k 1), ?_, hbig⟩
  have h := forwardMassSolution_of_momentFlow F a ω ℓ hΦ
  have e : (fun j => Φ s (Pi.single j 1)) = fun j => if R < (labelDist k j : ℝ) then 1 else 0 :=
    funext hinit
  rw [e] at h
  exact h

end BlockBand.Palm.MomentFlow
