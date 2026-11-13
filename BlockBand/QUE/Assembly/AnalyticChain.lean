module

public import BlockBand.QUE.Assembly.PhysicalAngularComplete
public import BlockBand.Window.SmallCriticalHolds
public import BlockBand.DeterminantScore.SpectralChainHolds

/-!
# The analytic chain of the physical angular theorem

Hypotheses: `NativeInputs`, `Prekopa.SourceContract`, `GUEWignerFamilyAdapter`,
`MDEBranchIdentification`, `ExternalETH`, `ExternalLocalGUE`, `GaussianLpGradient`,
`PhysicalBlockConditionalCount`, `MatchedTracesContract`, `RankLocationContract` (and, for the
small-critical theorem, `RingCompensatedPhaseContract`, `FreshCountContract`,
`PhysicalCenterContract`), `CoareaContract` (and, for the angular items, `FreshPalmContract`,
`FreshEigenpairDensityContract`, `PairPoleExclusionContract`), and the law bridges
`PairGUELawBridgeStatement`, `CompressedGUELawBridgeStatement`. Each theorem takes only the
hypotheses it uses.

* `physicalWeightedTrace_of_contracts`: the physical weighted trace estimate
  (`physicalWeightedTrace_holds`);
* `physicalRealLoop_of_contracts`: the physical real loop (`physicalRealLoop_of_weightedTrace`);
* `physicalMinorTail_of_contracts`: the physical minor tail (`physicalMinorTail_holds`);
* `determinantScore_of_contracts`: the determinant score theorem, both clauses
  (`determinantScore_holds`);
* `physicalAngularLabel_of_contracts`: the physical angular theorem for `0 < θ`
  (`physicalAngularLabel_of_good` with `goodPart_min_of`);
* `modeBound_of_center`: the mode bound for a Dyson centre family, from
  `QUE.PhysicalCenterContract` (`modeBound_of_contracts`);
* `smallCritical_of_center`: the small-critical theorem (`smallCritical_of_layerContracts`) for a Dyson
  centre family, from `QUE.PhysicalCenterContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.AnalyticChain

open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.DeterminantScore

/-- **The physical weighted trace estimate.** -/
theorem physicalWeightedTrace_of_contracts (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract) (hC : CoareaContract)
    (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement) :
    RealLoop.PhysicalWeightedTraceStatement :=
  WeightedTrace.physicalWeightedTrace_holds hC
    (BlockBand.LocalWindow.physicalLocalWindow_holds inputs hAd hMDE hETH hELG hPBC hMT hRank hC
      hBridge hComp)
    (SelectedIBPHolds.selectedResolvent_holds hBridge hELG hMDE hLp hPBC hMT hC hRank)

/-- **The physical real loop.** -/
theorem physicalRealLoop_of_contracts (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract) (hC : CoareaContract)
    (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalRealLoopStatement :=
  RealLoop.physicalRealLoop_of_weightedTrace hC
    (physicalWeightedTrace_of_contracts inputs hAd hMDE hETH hELG hLp hPBC hMT hRank hC hBridge hComp)

/-- **The physical minor tail.** -/
theorem physicalMinorTail_of_contracts (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract) (hC : CoareaContract)
    (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalMinorTailStatement :=
  MinorTailInverse.physicalMinorTail_holds hC (SpectralChainHolds.negativeSpread_holds hPre)
    (BlockBand.LocalWindow.physicalLocalWindow_holds inputs hAd hMDE hETH hELG hPBC hMT hRank hC
      hBridge hComp)
    (physicalRealLoop_of_contracts inputs hAd hMDE hETH hELG hLp hPBC hMT hRank hC hBridge hComp)

/-- **The determinant score theorem**, both clauses. -/
theorem determinantScore_of_contracts (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract) (hC : CoareaContract)
    (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement) :
    DeterminantScoreStatement :=
  DeterminantScoreHolds.determinantScore_holds hC
    (physicalMinorTail_of_contracts inputs hPre hAd hMDE hETH hELG hLp hPBC hMT hRank hC hBridge hComp)

/-- **The physical angular theorem** (`PhysicalAngularLabel`), `0 < θ`. -/
theorem physicalAngularLabel_of_contracts (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract)
    (hC : CoareaContract) (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    (hPole : PairPoleExclusionContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) :
    PhysicalAngularReduction.PhysicalAngularLabel b θ T hb hb' :=
  PhysicalAngularOfParts.physicalAngularLabel_of_good hb hb' hθ
    (Angular.AssemblyGood.goodPart_min_of hC hP hD
      (determinantScore_of_contracts inputs hPre hAd hMDE hETH hELG hLp hPBC hMT hRank hC hBridge hComp)
      hb hb' hθ)
    Angular.Assembly.pairRowNormTail_holds hPole

/-- **The mode bound** for a Dyson centre family, from `QUE.PhysicalCenterContract`. -/
theorem modeBound_of_center (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract)
    (hC : CoareaContract) (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    (hPole : PairPoleExclusionContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : IsCenterSupply w) (hc : PhysicalCenterContract b θ T hb hb' w) :
    WindowAngular.ModeBoundContract b θ T hb hb' :=
  ModeBoundOfContracts.modeBound_of_contracts b θ T hb hb' w hc
    (PhysicalAngularComplete.physicalAngularModeContract_holds inputs hPre hAd hMDE hETH hELG hLp hPBC
      hMT hRank hC hP hD hPole hBridge hComp hb hb' hθ w hw)

/-- **The small-critical theorem** (`WindowAngular.SmallCriticalContract`) for a Dyson centre
family `w`, from `QUE.PhysicalCenterContract` for `w`. -/
theorem smallCritical_of_center (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRing : RingCompensatedPhaseContract)
    (hRank : RankLocationContract) (hFresh : FreshCountContract)
    (hC : CoareaContract) (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    (hPole : PairPoleExclusionContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement)
    (w : PairCenterFamily) (hw : IsCenterSupply w)
    (hc : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      PhysicalCenterContract b θ T hb hb' w) :
    WindowAngular.SmallCriticalContract :=
  BlockBand.Window.smallCritical_of_layerContracts inputs hLp hMT hRing hRank hFresh w hc
    (fun _ _ _ hb hb' hθ _ =>
      PhysicalAngularComplete.physicalAngularModeContract_holds inputs hPre hAd hMDE hETH hELG hLp hPBC
        hMT hRank hC hP hD hPole hBridge hComp hb hb' hθ w hw)

end BlockBand.QUE.AnalyticChain
