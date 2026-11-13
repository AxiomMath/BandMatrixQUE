module

public import BlockBand.LocalWindow.Statements
public import BlockBand.Window.Count.GueNativeLawHolds
public import BlockBand.Angular.FiberAngular

/-!
# The pair `GUE` law bridge

The statement `PairGUELawBridgeStatement`: for `s > 0`, the `GUE` law on the pair sites at time
`pairTime p s` is the image of the `2W × 2W` source `GUE` law under `W ↦ √s W`, reindexed to the
pair sites by the coordinate equivalence `pairEquiv`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.LawBridge

open MeasureTheory Matrix BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs BlockBand.External
open BlockBand.SourceProcess

variable (p : Parameters) (i : ZMod p.n)

/-- The coordinate equivalence `PairSite p i ≃ Fin (2W)`. -/
def pairEquiv : PairSite p i ≃ Fin (2 * p.W) :=
  (Fintype.equivFin _).trans (finCongr (BlockBand.Angular.FiberAngular.card_pairSite p i))

/-- The `GUE` sample transported to the pair: `W ↦ reindex e⁻¹ e⁻¹ (√s W)`. -/
def pairSample (s : ℝ) (W : CEH.SourceHermitian (2 * p.W)) : PairMatrix p i :=
  reindex (pairEquiv p i).symm (pairEquiv p i).symm (((Real.sqrt s : ℝ) : ℂ) • W.1)

/-- **The pair `GUE` law bridge**: for every parameter set, pair and `s > 0`,
`GUE_{2W}(s/2W)` on the pair is the image of `gueSourceLaw (2W)` under `pairSample`.
-/
def PairGUELawBridgeStatement : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (s : ℝ), 0 < s →
    gueMeasure (PairSite p i) (pairTime p s) = (gueSourceLaw (2 * p.W)).map (pairSample p i s)

end BlockBand.LocalWindow.LawBridge
