module

public import BlockBand.Center.PhysicalCenterW0Inputs
public import BlockBand.Center.CenterIBPMain

/-!
# The physical center bound: final constructor

`physicalCenter_holds` proves the physical center bound for `pairCenterFamily0` for every
`0 < b < 1/2`, `θ > 0` and `T`, from the conditional block GUE count, the Gaussian `L^p`
gradient bound and pair pole exclusion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)

/-- **The physical center bound.**

*Statement.* For every `b ∈ (0, 1/2)`, every `θ` **with `0 < θ`** (for `θ ≤ 0`,
`IsBulkRank p θ α` admits spectral-edge ranks, where the theorem is not stated), and every `T`,
`QUE.PhysicalCenterContract b θ T hb hb' pairCenterFamily0` holds: there are `B ≥ 0` and
`W₀ : ℝ` such that for all `n ≥ 4`, `W ≥ 1` with `n ≤ TW` and `W₀ < W` (strict, `W₀` the
smooth-center threshold at `q = 4`), every model, every `θ`-bulk rank `α` and every adjacent pair
`i`, `E♯_{α,i} |j_i(λ_α)|² ≤ B/(√n W^{3/2})`.
*Law.* The exact pair law (`extendedPairMeasure p α i X.P X.Hm`, density
`(n/2)(p_{αi} + p_{α,i+1})`) of the witness extension of `pairCenterFamily0`, whose center is the
Dyson center `j_i(λ_α)` built from `H - G_i` (extended by zero off the regular domain of `cst0`);
internally transported to the exact simultaneous splitting of `pcSplittingExists_holds`.
*Domain.* `0 < b < 1/2`, `0 < θ`, `T ∈ ℝ`; `4 ≤ n`, `0 < W`, `n ≤ TW`, `W₀ < W`.
*Norms.* Real second moment of the center under the pair law (internally: `L⁴` moments of the
smooth center and its shift derivatives, `L⁴` rank location, `L²` divergence).
*Quantifier order / uniformity.* `b, θ, T` first; then `B, W₀`, depending on `(b, θ, T)` only;
then `n, W`, the model, `α`, `i`.
*Order of limits.* None (fixed-`(n, W)` inequality).
*Hypotheses.* `Inputs.ConditionalBlockGUECount`, `Inputs.GaussianLpGradient` and
`CoareaPalm.PairPoleExclusionContract` (only through `centerDomainContract_cst0_holds`); no other
hypothesis.
*Used.* `physicalCenter_holds_of_W0` (with `pcSplittingExists_holds`, `pcCenterCyclic_holds`),
`smoothCenterW0_holds_of`, `taggedTrace_holds`, `centerDomainContract_cst0_holds`,
`rankLocation_holds`, `pcEnergyPrimitive_holds`, `pcDivergenceIsometry_holds`.
`SmoothCenterW0 cst0` is proved here from the hypotheses above; `SmoothCenterContract` is not
used. -/
theorem physicalCenter_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hpole : PairPoleExclusionContract) :
    ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ →
      PhysicalCenterContract b θ T hb hb' pairCenterFamily0 :=
  physicalCenter_holds_of_W0 (BlockBand.Layers.rankLocation_holds hcount hgrad)
    (smoothCenterW0_holds_of (BlockBand.Layers.taggedTrace_holds hcount hgrad)
      (centerDomainContract_cst0_holds hcount hgrad hpole))
    pcEnergyPrimitive_holds pcDivergenceIsometry_holds

end BlockBand.Center
