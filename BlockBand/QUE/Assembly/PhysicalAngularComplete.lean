module

public import BlockBand.QUE.Assembly.PhysicalAngularFinal
public import BlockBand.LocalWindow.ProofPartTwoHolds

/-!
# `QUE.PhysicalAngularModeContract` from the external and internal inputs

`physicalAngularModeContract_holds`: the physical angular theorem at `φ = conj A_m`, for every
Dyson centre family and `0 < θ`, from the external inputs (Prékopa, local laws, ETH, Gaussian
`L^p` gradient), the Palm and coarea statements, and the two law-bridge statements taken as
hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.PhysicalAngularComplete

open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.External BlockBand.LocalWindow.LawBridge

/-- **The physical angular theorem** (`QUE.PhysicalAngularModeContract`, at `φ = conj A_m`), for
every Dyson centre family and `0 < θ`. -/
theorem physicalAngularModeContract_holds (inputs : NativeInputs.{0})
    (hPre : BlockBand.External.Prekopa.SourceContract) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract)
    (hC : CoareaContract) (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    (hPole : PairPoleExclusionContract)
    (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : IsCenterSupply w) :
    PhysicalAngularModeContract b θ T hb hb' w :=
  PhysicalAngularFinal.physicalAngularModeContract_of_localWindow hC hP hD hPole hPre hBridge hELG
    hMDE hLp hPBC hMT hRank
    (BlockBand.LocalWindow.physicalLocalWindow_holds inputs hAd hMDE hETH hELG hPBC hMT hRank hC
      hBridge hComp) hb hb' hθ w hw

end BlockBand.QUE.PhysicalAngularComplete
