module

public import BlockBand.Layers.BUniformClock
public import BlockBand.Layers.BUniformAbsorption

/-!
# The clock-mean identity, `b`-uniform: the constructor

The `b`-uniform clock-mean identity `LayersBUniform.ClockMeanUniformContract` from the
conditional block-GUE count, by applying `bu_clockMeanUniform_of` to the uniform Gaussian
absorption clause `gaussianAbsorptionUniform_holds`. The only hypothesis is
`Inputs.ConditionalBlockGUECount`. Law, domain and uniformity are those of the contract: `β ∈ (0,1/4)`,
`κ > 0`; then `d_* > 0`, `C`, `W₀`; then uniformly in `b ∈ [β, 1/2 - β]`, `W ≥ W₀`, Hermitian `X`,
`E ∈ bulkInterval κ` with `d(X) ≤ d_*`, `Y ⪰ 0`; law `layerLaw W b .separate`; `ℓ²` operator norm.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)

/-- The clock-mean identity, uniformly in `b`, from `ConditionalBlockGUECount`. -/
theorem clockMeanUniform_holds (hcount : ConditionalBlockGUECount) :
    BlockBand.Internal.Contracts.LayersBUniform.ClockMeanUniformContract :=
  bu_clockMeanUniform_of (gaussianAbsorptionUniform_holds hcount)

end BlockBand.Layers
