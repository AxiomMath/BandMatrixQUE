module

public import BlockBand.Layers.OnePortSD
public import BlockBand.Layers.OnePortMean

/-!
# The one-port passive mean (`OnePortPassiveMeanContract`)

The constructor of `OnePortPassiveMeanContract` from `ConditionalBlockGUECount` and
`GaussianLpGradient`: the proof of the passive Schwinger–Dyson system
(`oppPassiveMeanEquations_holds`) is substituted into the reduction
`onePortPassiveMean_holds_of_meanEquations`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount GaussianLpGradient)

/-- **One-port passive mean** (`LayersOnePort.OnePortPassiveMeanContract`): "the passive mean
`E_j LL* ⪯ (1 + Cδ₀ + CW⁻²) I`", from the passive mean identity, the exact identity and the
passive-bounds lemma.

* **Law / measure.** The fresh one-block one-port layer `layerLaw W b .oneBlockOnePort`
  (`A ~ GUE_W(c/W)`, `c = 1 - 2b`, `B ~ Gin(b/W)` independent) at `z = z_∂(E)`; expectations over
  the fresh layer only, conditional on the deterministic (independent) input `X`;
  `L = K𝒢₁₂`, `K = z - X`, `δ₀ = onePortDistance b E X = |W⁻¹ Tr(z - X)⁻¹ - a|`.
* **Domain.** `b ∈ (0,1/2)`, `κ > 0`, `E ∈ bulkInterval κ`, `W ≥ W₀`, every passive `X`
  (`-Im X ⪰ 0`; no bound on `‖X‖` or `‖Im X‖`; no scalar- or jet-domain restriction).
* **Norms.** Euclidean operator norm on `W × W` matrices; the Loewner order `M ⪯ λI` as
  `(λI - M).PosSemidef`; entrywise expectations (`matrixExpect`).
* **Conclusion.** The entries of `LL*` are integrable and `E LL* ⪯ (1 + Cδ₀ + CW⁻²) I`.
* **Quantifier order / uniformity.** `b, κ` first; then `C ≥ 0`, `W₀` (depending only on
  `b, κ`); then uniformly in `W ≥ W₀`, passive `X` and `E ∈ bulkInterval κ`. No order of limits.
* **Proof.** `onePortPassiveMean_holds_of_meanEquations hcount hsd` (passive
  inverse moments and operator moments from `OnePortMoments`, the deterministic reduction
  `opp_core_bound` on `δ₀ ≤ d₁`, the crude moment bound on `δ₀ > d₁`), with the passive
  Schwinger–Dyson system `hsd := oppPassiveMeanEquations_holds hcount hgrad`.
* **Inputs.** `ConditionalBlockGUECount` (used) and `GaussianLpGradient` (accepted, not needed
  by the proof: see `oppPassiveMeanEquations_holds`). -/
theorem onePortPassiveMean_holds (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : OnePortPassiveMeanContract :=
  onePortPassiveMean_holds_of_meanEquations hcount (oppPassiveMeanEquations_holds hcount hgrad)

end BlockBand.Layers
