module

public import BlockBand.LocalWindow.LawBridgeStatement

/-!
# The compressed pair `GUE` law bridge

For `|ρ| > W^H`, let `Q_w = I - ww*` and compress to `w^⊥`. The compressed fresh noise is exactly
`GUE_{d-1}(t)`, with total variance `s' = s(1 - 1/d)`.

In the large-`ρ` range the external eigenstate thermalization theorem is applied to the
`(2W - 1)`-dimensional block `U_w* G U_w` (`U_w` an isometry onto `w^⊥`). `Inputs.ExternalETH`
is stated for `gueSourceLaw N = GUE_N(1/N)` scaled by `√s'`; the pair law bridge
`LawBridge.PairGUELawBridgeStatement` covers only the full pair block. The needed identity of
measures is recorded here as a named statement (proved as `compressedGUELawBridge_holds`): for every
isometry
`U : ℂ^{2W-1} → ℂ^{PairSite}` (`U* U = 1`), the image of `GUE_{2W}(s/2W)` under `G ↦ U* G U` is
the image of `gueSourceLaw (2W - 1)` under `W ↦ √(s(1 - 1/(2W))) W`.

This is an exact Gaussian identity (unitary invariance of `GUE` and the restriction of `GUE_d(t)`
to a principal `(d-1)`-block; entry variance `t = s/d = s'/(d-1)`), not an estimate of the paper.
It is a hypothesis of the large-`ρ` step, in the same way as the pair bridge.

Definition only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs BlockBand.External

/-- **The compressed pair `GUE` law bridge**: for every parameter set, pair, `s > 0` and isometry
`U : Fin (2W - 1) → PairSite` (`U* U = 1`), the compression `U* G U` of `G ~ GUE_{2W}(s/2W)` has
the law of `√(s(1 - 1/(2W))) W`, `W ~ gueSourceLaw (2W - 1)`. -/
def CompressedGUELawBridgeStatement : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (s : ℝ), 0 < s →
    ∀ U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ, Uᴴ * U = 1 →
      (gueMeasure (PairSite p i) (pairTime p s)).map (fun G => Uᴴ * G * U) =
        (gueSourceLaw (2 * p.W - 1)).map
          (fun W => (((Real.sqrt (s * (1 - 1 / (2 * (p.W : ℝ))))) : ℝ) : ℂ) • W.1)

end BlockBand.LocalWindow.ProofPartTwo
