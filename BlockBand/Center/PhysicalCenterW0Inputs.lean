module

public import BlockBand.Center.PhysicalCenterW0
public import BlockBand.Center.CenterSupplyHolds
public import BlockBand.Layers.TaggedTraceHolds

/-!
# The physical center bound from the two integration-by-parts inputs

`physicalCenter_holds_of_inputs`: `physicalCenter_holds_of_W0` with rank location
(`rankLocation_holds`), the thresholded smooth center (`smoothCenterW0_holds_of` from
`taggedTrace_holds` and `centerDomainContract_cst0_holds`); the hypotheses are
`ConditionalBlockGUECount`, `GaussianLpGradient`, `PairPoleExclusionContract`,
`PcEnergyPrimitive` and `PcDivergenceIsometry`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)

/-- **The physical center bound.** For every `b ∈ (0, 1/2)`, `θ > 0` and `T` there are `B ≥ 0`
and `W₀` such that for all `n ≥ 4`, `W ≥ 1`, `n ≤ TW`, `W > W₀`, every model, `θ`-bulk rank `α`
and adjacent pair `i`: `E♯_{α,i} |j_i(λ_α)|² ≤ B/(√n W^{3/2})` under the pair law
`extendedPairMeasure`.

*Law.* The exact pair law `extendedPairMeasure` of the witness extension of `pairCenterFamily0`
(as in `physicalCenter_holds_of_W0`).
*Domain.* `0 < b < 1/2`, `θ > 0`, `T` arbitrary.
*Norms.* Real second moment of the center under the pair law.
*Quantifier order / uniformity.* `b, θ, T` first, then `B, W₀` (from `(b, θ, T)` only), then
`n, W`, the model, `α`, `i`.
*Order of limits.* None.
*Hypotheses.* `Inputs.ConditionalBlockGUECount`, `Inputs.GaussianLpGradient`,
`CoareaPalm.PairPoleExclusionContract` (through `centerDomainContract_cst0_holds`),
`PcEnergyPrimitive` and `PcDivergenceIsometry` (the last two are proved as
`pcEnergyPrimitive_holds` and `pcDivergenceIsometry_holds`, see `physicalCenter_holds`).
*Used.* `rankLocation_holds`, `taggedTrace_holds`, `centerDomainContract_cst0_holds`,
`smoothCenterW0_holds_of`, `physicalCenter_holds_of_W0` (with `pcSplittingExists_holds`,
`pcCenterCyclic_holds`). -/
theorem physicalCenter_holds_of_inputs (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) (hpole : PairPoleExclusionContract)
    (henergy : PcEnergyPrimitive) (hiso : PcDivergenceIsometry) :
    ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ →
      PhysicalCenterContract b θ T hb hb' pairCenterFamily0 :=
  physicalCenter_holds_of_W0 (BlockBand.Layers.rankLocation_holds hcount hgrad)
    (smoothCenterW0_holds_of (BlockBand.Layers.taggedTrace_holds hcount hgrad)
      (centerDomainContract_cst0_holds hcount hgrad hpole))
    henergy hiso

end BlockBand.Center
