module

public import BlockBand.Critical.CommonPort.Moments
public import BlockBand.Critical.CommonPort.Fluctuation
public import BlockBand.Critical.CommonPort.Ladder
public import BlockBand.Critical.CommonPort.Comparison
public import BlockBand.Critical.CommonPort.SchwingerDyson
public import BlockBand.Critical.CommonPort.WeightedCov
public import BlockBand.Critical.CommonPort.Residuals
public import BlockBand.Critical.CommonPort.Mean
public import BlockBand.Critical.CommonPort.MeanAssembly
public import BlockBand.Critical.CommonPort.MeanClause

/-!
# The common-port mean lemma

This file collects the proof of the common-port mean lemma, which establishes all fields of
`CommonPortMeanContract` for the law `layerLaw W b .common`, conditionally on the
deformation (every deterministic Hermitian `X`).

## Main results

* `BlockBand.Critical.CommonPort.commonPortMean_moments (hGA) :` the `moments` field of
  `Critical.CommonPortMeanContract` (fresh operator moments of `L = K𝒢₁₂`, `H = 𝒢₂₂`, every fixed
  `p ≥ 1`, uniformly in the Hermitian deformation and `e ∈ bulkInterval κ`).
* `BlockBand.Critical.CommonPort.commonPortMean_fluctuation (hGA) :` the `fluctuation` field
  (`‖u*{LL* - E LL*}v‖_p ≤ C_p W^{-1/2}‖u‖‖v‖`, every fixed `p ≥ 2`, arbitrary `u, v`).
* `BlockBand.Critical.CommonPort.commonPortMean_mean (hGA) (hLC) :` the `mean` field
  (`‖E(LL*) - γ I‖ ≤ C(δ + W⁻²)` on `δ ≤ δ₀`).
* `BlockBand.Critical.CommonPort.commonPortMean_holds (hGA) (hLC) :
  Critical.CommonPortMeanContract`.
-/
