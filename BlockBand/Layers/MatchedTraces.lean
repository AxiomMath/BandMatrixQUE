module

public import BlockBand.Layers.MatchedPath
public import BlockBand.Layers.RingTraces
public import BlockBand.Layers.ResidualSplitLaw
public import BlockBand.Layers.ResidualLayer

/-!
# The matched-traces theorem: assembled constructor

All three fields of `MatchedTracesContract`, from `ConditionalBlockGUECount` and
`GaussianLpGradient` (`matchedTraces_holds`). Each field is supplied by a result of another module:

* the path field (the matched-trace moments): `matchedTracesPath_holds` (cores `coreTraces_holds`, path growth,
  stopped scalar recursion; every `1 ≤ r ≤ TW`, both parities, law `pathLaw W r b`);
* the common-port field (the common-port trace): `commonPort_of_path` (exact ring law, split into a common-port
  layer and a path of `n − 3` blocks, the layer-contraction lemma common clause, trace fluctuation), for the
  exact physical ring, `4 ≤ n ≤ TW`, every block `k`;
* the residual-pair field: `residualPair_of_path` with the pair-splitting law
  identified (`residualSplitLaw_holds`) and the residual layer bound
  (`residualPairLayerBound_holds`), for every `0 < s < 2 min(c,b)`.

Norms: `L^p` of the modulus of normalized traces; constants chosen from `(b, κ, T)` (and `s`)
before `W, p`, the model and the data.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts

/-- **The matched-traces theorem**, constructor of `MatchedTracesContract`, from
`ConditionalBlockGUECount` and `GaussianLpGradient`. -/
theorem matchedTraces_holds (hcount : Inputs.ConditionalBlockGUECount)
    (hgrad : Inputs.GaussianLpGradient) : Layers.MatchedTracesContract :=
  { path := matchedTracesPath_holds hcount hgrad
    commonPort := commonPort_of_path hcount hgrad (matchedTracesPath_holds hcount hgrad)
    residualPair := residualPair_of_path (matchedTracesPath_holds hcount hgrad)
      residualSplitLaw_holds (residualPairLayerBound_holds hcount hgrad) }

end BlockBand.Layers
