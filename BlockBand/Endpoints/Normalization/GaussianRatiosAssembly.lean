module

public import BlockBand.Endpoints.Normalization.GaussianRatios
public import BlockBand.Endpoints.Normalization.Normalizer

/-!
# The Gaussian-ratios theorem and the two-positive-clocks lemma (Palm part) from the contracts

This module discharges the hypothesis `NormalizerLowerBound` with the deterministic-normalizer
corollary (`deterministic_normalizer_lower`). On the class, `FreshRegular` gives
`v₀ ≤ Im m_{F,c₀}(E)` (variance `s = c₀`, energy `x = E`, height `η = 0`), so with `v_* = v₀` we
get `palmMass ≥ (v₀/2π) N` for `N ≥ max N₀ 1`. The results are `GaussianRatiosContract` and
`TwoPositiveClocksPalmContract`, from `FreshPalmContract`, `FreshEigenpairDensityContract` and
`PointDensityContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical

/-- `NormalizerLowerBound` from the deterministic-normalizer corollary, with `c = v₀/(2π)`. -/
theorem normalizerLowerBound_of (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract) : NormalizerLowerBound := by
  intro A c₀ r₀ s₀ v₀ hFC
  have hv : 0 < v₀ := hFC.2.2.2.2.2
  obtain ⟨N₀, hN₀⟩ := deterministic_normalizer_lower hPD hD A c₀ r₀ s₀ v₀ hFC v₀ hv
  refine ⟨v₀ / (2 * Real.pi), by positivity, max N₀ 1, fun N hN F E hF => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hN)
  have hreg := hF.2.2 c₀ ⟨by linarith [hFC.2.2.2.1], le_rfl⟩ E (by simp [hFC.2.2.1.le])
    0 ⟨le_rfl, zero_le_one⟩
  have hm : v₀ ≤ (freshDyson F c₀ E).im := by
    have h1 := hreg.1
    have heq : (⟨E, 0⟩ : ℂ) = (E : ℂ) := rfl
    rwa [heq] at h1
  exact hN₀ N hN1 (le_of_max_le_left hN) F E hF hm

/-- **The Gaussian-ratios theorem** from `FreshPalmContract`, `FreshEigenpairDensityContract` and
`PointDensityContract`.
-/
theorem gaussianRatios_of_contracts (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract) : GaussianRatiosContract :=
  gaussianRatios_of hP (normalizerLowerBound_of hPD hD)

/-- **Two-positive-clocks lemma, Palm part**, from the same contracts. -/
theorem twoPositiveClocksPalm_of_contracts (hP : FreshPalmContract)
    (hPD : PointDensityContract) (hD : FreshEigenpairDensityContract) :
    TwoPositiveClocksPalmContract :=
  twoPositiveClocksPalm_of hP (normalizerLowerBound_of hPD hD)

end BlockBand.Endpoints.Normalization
