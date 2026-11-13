module

public import BlockBand.Palm.MomentFlow.StepsLong
public import BlockBand.Palm.MomentFlow.BridgeIdentity
public import BlockBand.Palm.GoodEventHolds

/-!
# Long couplings along the flow on the spectral good event

* `long_flow_coupling_le` (pathwise): if the long-gap clause holds at time `s` and the spectrum
  is simple, `∑_{|j-i| ≥ ℓ} c_ij(s) X_j(s) ≤ (2N/(c₁ℓ)) Im q*(H_s - λ_i(s) - i c₁ℓ/N)⁻¹ q`.
* `long_flow_coupling_event` (from `spectralGoodEvent_s8`): the same, simultaneously for all
  `s ∈ [a, c]`, all labels `i`, outside an outer `flowLaw N a`-probability `N^{-D}`, for every `ω`
  with Hermitian `ω.1` and simple spectrum at `s`. (The displacement clause is part of the same
  good event.)
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs

variable {N : ℕ}

theorem long_flow_coupling_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s : ℝ}
    {ω : FlowSample N} (hH : ω.1.IsHermitian) (hs : HasSimpleSpectrum N (flowMatrix F a ω s))
    (hN : 0 < N) {c₁ : ℝ} (hc : 0 < c₁) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|)
    (q : Fin N → ℂ) (i : Fin N) :
    ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
        flowRate F a ω s i j * flowOverlap F a q s j ω ≤
      2 / (c₁ * ℓ / N) * (star q ⬝ᵥ ((flowMatrix F a ω s -
        (⟨flowEigenvalue F a ω s i, c₁ * ℓ / N⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im :=
  long_rank_coupling_sum_le (flowMatrix_isHermitian hF a hH s) hs hN hc hℓ hgap q i

/-- **Long couplings on the spectral good event.** -/
theorem long_flow_coupling_event (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (A c r₀ s₀ v₀ : ℝ) (hK : FreshConstants c r₀ s₀ v₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
        let a : ℝ := c - τ
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        ∃ Bad : Set (FlowSample N), flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ s ∈ Set.Icc a c,
            HasSimpleSpectrum N (flowMatrix F a ω s) → 0 < N → 0 < ℓ →
            ∀ (q : Fin N → ℂ) (i : Fin N),
              ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
                  flowRate F a ω s i j * flowOverlap F a q s j ω ≤
                2 / (c₁ * ℓ / N) * (star q ⬝ᵥ ((flowMatrix F a ω s -
                  (⟨flowEigenvalue F a ω s i, c₁ * ℓ / N⟩ : ℂ) •
                    (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
  obtain ⟨c₁, C₁, C, b₀, hc₁, _, _, _, hD⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  refine ⟨c₁, hc₁, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hD D
  refine ⟨N₀, fun N hN F E hC => ?_⟩
  intro τ a ℓ
  refine ⟨_, hN₀ N hN F E hC, fun ω hω hH s hsI hs hNp hℓ q i => ?_⟩
  have hgood := not_not.1 hω s hsI
  obtain ⟨hF, -, -⟩ := hC
  exact long_flow_coupling_le hF hH hs hNp hc₁ hℓ hgood.1 q i

end BlockBand.Palm.MomentFlow
