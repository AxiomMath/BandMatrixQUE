module

public import BlockBand.QUE.Assembly.PhysicalAngularHolds
public import BlockBand.DeterminantScore.SelectedIBPHolds
public import BlockBand.LocalWindow.ProofPartOne

/-!
# `QUE.PhysicalAngularModeContract` from part (ii) of the local window

* `physicalAngularModeContract_of_localWindow`: `physicalAngularModeContract_of_window` with
  `SelectedResolventStatement` discharged by `selectedResolvent_holds`. The hypotheses are
  `PhysicalLocalWindowStatement`, `CoareaContract`, `FreshPalmContract`,
  `FreshEigenpairDensityContract`, `PairPoleExclusionContract`, `Prekopa.SourceContract`,
  `PairGUELawBridgeStatement`, `ExternalLocalGUE`, `MDEBranchIdentification`,
  `GaussianLpGradient`, `PhysicalBlockConditionalCount`, `MatchedTracesContract` and
  `RankLocationContract`.
* `physicalAngularModeContract_of_partTwo`: the same with part (i) discharged by
  `physicalLocalWindow_partOne` and `physicalLocalWindow_of_parts`.
  `PhysicalLocalWindowStatement` is replaced by `PhysicalLocalWindowPartTwoStatement`; the other
  hypotheses are unchanged.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PhysicalAngularFinal

open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow.LawBridge

/-- **The physical angular theorem from the local window**, for every Dyson centre family,
`0 < θ`. -/
theorem physicalAngularModeContract_of_localWindow (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRank : RankLocationContract)
    (hLW : BlockBand.LocalWindow.PhysicalLocalWindowStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  PhysicalAngularHolds.physicalAngularModeContract_of_window hC hP hD hPole hPre hLW
    (BlockBand.DeterminantScore.SelectedIBPHolds.selectedResolvent_holds hBridge hELG hMDE hLp hPBC hMT hC
      hRank) hb hb' hθ w hw

/-- **The physical angular theorem from part (ii) of the local window**, for every Dyson centre
family, `0 < θ`. -/
theorem physicalAngularModeContract_of_partTwo (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hPole : PairPoleExclusionContract)
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRank : RankLocationContract)
    (h2 : BlockBand.LocalWindow.PhysicalLocalWindowPartTwoStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  physicalAngularModeContract_of_localWindow hC hP hD hPole hPre hBridge hELG hMDE hLp hPBC hMT hRank
    (BlockBand.LocalWindow.physicalLocalWindow_of_parts
      (BlockBand.LocalWindow.physicalLocalWindow_partOne hBridge hELG hMDE hPBC hMT hRank hC) h2)
    hb hb' hθ w hw

end BlockBand.QUE.PhysicalAngularFinal
