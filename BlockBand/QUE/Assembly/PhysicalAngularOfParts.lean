module

public import BlockBand.Angular.AssemblyEigen
public import BlockBand.DeterminantScore.GUENormTailProof
public import BlockBand.Angular.AssemblyRowTail

/-!
# `QUE.PhysicalAngularModeContract` from the parts of the physical angular theorem

The physical angular theorem is assembled from three statements: the good-event part of the
proof `Assembly.GoodPartStatement`, the pair-row norm event `Assembly.PairRowNormTailStatement`
(proved unconditionally as `pairRowNormTail_holds`), and the pole event
`CoareaPalm.PairPoleExclusionContract`.

* `physicalAngularLabel_of_good`, `physicalAngularModeContract_of_good`: the physical angular
  theorem from the three statements (the GUE norm tail is discharged by `gueNormTail_holds`);
* `physicalAngularModeContract_of_goodPart`: the same with the pair-row norm event discharged.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PhysicalAngularOfParts

open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.QUE.PhysicalAngularReduction BlockBand.Angular.Assembly

/-- **The physical angular theorem for `0 < θ`**, without the norm-tail hypothesis. -/
theorem physicalAngularLabel_of_good {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ)
    (hGood : GoodPartStatement b (min θ (1 / 4)) T hb hb') (hRow : PairRowNormTailStatement)
    (hPole : PairPoleExclusionContract) : PhysicalAngularLabel b θ T hb hb' :=
  physicalAngularLabel_of hb hb' hθ hGood
    BlockBand.DeterminantScore.GUENormTail.gueNormTail_holds hRow hPole

/-- **The physical angular statement `QUE.PhysicalAngularModeContract`** for every Dyson centre
family, `0 < θ`. -/
theorem physicalAngularModeContract_of_good {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hGood : GoodPartStatement b (min θ (1 / 4)) T hb hb')
    (hRow : PairRowNormTailStatement) (hPole : PairPoleExclusionContract)
    (w : PairCenterFamily) (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_label b θ T hb hb'
    (physicalAngularLabel_of_good hb hb' hθ hGood hRow hPole) w hw

/-- **`QUE.PhysicalAngularModeContract`** from `GoodPartStatement` and the pole exclusion only
(both Gaussian tails discharged), for every Dyson centre family, `0 < θ`. -/
theorem physicalAngularModeContract_of_goodPart {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hGood : GoodPartStatement b (min θ (1 / 4)) T hb hb')
    (hPole : PairPoleExclusionContract)
    (w : PairCenterFamily) (hw : BlockBand.Internal.Contracts.Layers.IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_good hb hb' hθ hGood pairRowNormTail_holds hPole w hw

end BlockBand.QUE.PhysicalAngularOfParts
