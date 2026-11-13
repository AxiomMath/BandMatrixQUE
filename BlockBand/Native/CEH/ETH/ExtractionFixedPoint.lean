module

public import BlockBand.Native.CEH.ETH.Adapter

/-!
# CEH ETH: extraction from the fixed-point `θ = 1` bound

The regular-window ETH bound and the external ETH statement follow from the bound form
`FixedPointPositiveChainLawThetaOne gue` of the positive-chain law (the form CEH (4.4) states for
the `Im G A Im G` chain).

## Main results

* `measure_localETHWindowBad_le_of_fixedPointThetaOne`: extraction at a small height exponent.
  The law is evaluated only at grid pairs, where `θ = 1` holds by
  `regularizationCoefficient_gridPair_eq_one`.
* `localETHRegularWindowBound_of_fixedPointThetaOne`: the conclusion
  `LocalETHRegularWindowBound gue`.
* `externalETH_of_fixedPointThetaOne`: composed with the adapter
  `externalETH_of_localETHRegularWindowBound`, `Inputs.ExternalETH`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set Filter
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH CEHNative.BlockBand.CEH
open scoped Matrix Matrix.Norms.L2Operator ENNReal

/-- **Extraction at a small height exponent from the fixed-point `θ = 1` bound.** With hypothesis
`FixedPointPositiveChainLawThetaOne gue`: for `0 < ξ < δ`, `ξ < 1/2`, the bad event at `(ξ, δ)`
has probability at most `N^(-D)`, eventually in `N` and uniformly in the quantifiers of
`LocalETHRegularWindowBound`. -/
theorem measure_localETHWindowBad_le_of_fixedPointThetaOne
    (gue : LocalETHGUEFamily) (hlaw : FixedPointPositiveChainLawThetaOne gue)
    {κ C sLo sHi r c K β ξ δ D : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C)
    (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hβ : β < 1) (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hξδ : ξ < δ) (hD : 0 < D) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hε : 0 < δ - ξ := by linarith
  refine measure_localETHWindowBad_le_of_gridTail gue hsLo hsHi hr hc hK hβ hξ hξhalf
    hξδ ?_
  obtain ⟨Nlaw, hNlaw⟩ := hlaw κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK
    (ξ / 2) (2 * ξ) (by positivity) (by linarith) (by linarith)
    (δ - ξ) (D + 20) hε (by linarith)
  obtain ⟨Ndet, hNdet⟩ := eventually_atTop.1
    (eventually_cehETHGridScalarConditions (δ := δ) (ε := δ - ξ) hsLo hsHi hr hc hK hβ
      hξ hξhalf hε (by linarith))
  obtain ⟨Nconv, hNconv⟩ := eventually_atTop.1
    (eventually_cehTwoResolventLaw_conversionConditions (β := β) (K := K) hsLo hsHi hc
      hK.le hβ hξ (by linarith) hε)
  refine ⟨max Nlaw (max Ndet Nconv), ?_⟩
  intro N hN s hs hsH F hFdef Mf hMf E₀ hreg J hJh hJ a b
  obtain ⟨hN4, hall⟩ := hNdet N (le_of_max_le_left (le_of_max_le_right hN))
  obtain ⟨hcond, hlo, hHup⟩ := hall s hs hsH
  have hconv := hNconv N (le_of_max_le_right (le_of_max_le_right hN)) s hs hsH
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hN0 : 0 < N := by omega
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  have hma := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) a
  have hmb := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) b
  have hHq := (canonicalHeightRate_lt_quantitativeIFTHeight hN0 hc hcond.2.1).le
  have htheta := regularizationCoefficient_gridPair_eq_one hN0 hs0 F hMf hr hc hreg
    (by positivity : 0 < N ^ 4) hcond.1 hHq
    ⟨hconv.1, hconv.2.1, hconv.2.2.1, hconv.2.2.2.1⟩ a b
  exact hNlaw N (le_of_max_le_left hN) s hs hsH F hFdef Mf hMf E₀ hreg
    _ _ hma.2.1 hmb.2.1 (hlo.trans hma.2.2.1) (hma.2.2.2.1.trans hHup)
    (hlo.trans hmb.2.2.1) (hmb.2.2.2.1.trans hHup) htheta J hJh hJ

/-- **The regular-window ETH bound from the fixed-point `θ = 1` bound.** For an arbitrary family
`gue`, `FixedPointPositiveChainLawThetaOne gue` implies `LocalETHRegularWindowBound gue`
(auxiliary height `ξ' = min(ξ, δ/4)`, auxiliary loss `δ/2`, centre comparison
`centreComparison_regularWindow`). -/
theorem localETHRegularWindowBound_of_fixedPointThetaOne
    (gue : LocalETHGUEFamily) (hlaw : FixedPointPositiveChainLawThetaOne gue) :
    LocalETHRegularWindowBound gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK β hβ hβ2 ξ hξ hξβ δ D hδ hD
  set ξ' : ℝ := min ξ (δ / 4) with hξ'def
  have hξ'pos : 0 < ξ' := lt_min hξ (by positivity)
  have hξ'ξ : ξ' ≤ ξ := min_le_left _ _
  have hξ'δ : ξ' ≤ δ / 4 := min_le_right _ _
  have hβ1 : β < 1 := lt_of_le_of_lt hβ2 (by norm_num)
  exact CEH.localETHWindowBad_polynomialTail_of_auxiliaryLoss gue
    (ξ' := ξ') (δ' := δ / 2) hsLo hr hc hK hξ hξβ hβ2 hξ'pos.le hξ'ξ hδ (by linarith)
    (measure_localETHWindowBad_le_of_fixedPointThetaOne gue hlaw hκ hC hsLo
      hsHi hr hc hK hβ1 hξ'pos (by linarith) (by linarith) hD)

/-- The fixed-point `θ = 1` bound at the GUE family implies `Inputs.ExternalETH`. -/
theorem externalETH_of_fixedPointThetaOne
    (hlaw : FixedPointPositiveChainLawThetaOne gueLawFamily) :
    BlockBand.Internal.Contracts.Inputs.ExternalETH :=
  externalETH_of_localETHRegularWindowBound
    (localETHRegularWindowBound_of_fixedPointThetaOne gueLawFamily hlaw)

end BlockBand.Native.CEH.ETH
