module

public import BlockBand.QUE.Assembly.AnalyticChain
public import BlockBand.QUE.GUEInputs.PhysicalAngular
public import BlockBand.Internal.ReducedInputs.WindowPsss

/-!
# The mode bound and the small-ratio critical theorem from GUE-scope inputs

Versions of `QUE.AnalyticChain.modeBound_of_center` and `QUE.AnalyticChain.smallCritical_of_center`
in which the bundled inputs are replaced by the specific GUE-scope hypotheses they use: the
existence of eigenpair selections and typical spacing for the CEH local law, and the PSSS
source theorem.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.ReducedInputs

open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.External BlockBand.LocalWindow.LawBridge

/-- `QUE.AnalyticChain.modeBound_of_center` with the hypotheses `hEig`, `hSp` in place of `inputs`
and `hAd`. -/
theorem modeBound_of_center_gueInputs
    (hEig : ∀ (N : ℕ), 0 < N → Nonempty (CEH.EigenpairSelection N))
    (hSp : ∀ {N : ℕ} {lambda : ℝ} {H0 : CEH.SourceHermitian N},
      4 ≤ N → 0 < lambda → ∀ M : CEH.MDEBranch lambda H0, Nonempty (CEH.TypicalSpacing M))
    (hPre : BlockBand.External.Prekopa.SourceContract)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hLp : GaussianLpGradient) (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRank : RankLocationContract)
    (hC : CoareaContract) (hP : FreshPalmContract) (hD : FreshEigenpairDensityContract)
    (hPole : PairPoleExclusionContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : BlockBand.LocalWindow.ProofPartTwo.CompressedGUELawBridgeStatement)
    {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (w : PairCenterFamily)
    (hw : IsCenterSupply w) (hc : PhysicalCenterContract b θ T hb hb' w) :
    WindowAngular.ModeBoundContract b θ T hb hb' :=
  BlockBand.QUE.ModeBoundOfContracts.modeBound_of_contracts b θ T hb hb' w hc
    (BlockBand.QUE.GUEInputs.physicalAngularModeContract_of_gueInputs hEig hSp hPre hMDE hETH hELG hLp hPBC
      hMT hRank hC hP hD hPole hBridge hComp hb hb' hθ w hw)

/-- `QUE.AnalyticChain.smallCritical_of_center` with `inputs`, `hAd` replaced by `hpsss`, `hEig`,
`hSp`: `WindowAngular.SmallCriticalContract`. -/
theorem smallCritical_of_center_gueInputs (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hEig : ∀ (N : ℕ), 0 < N → Nonempty (CEH.EigenpairSelection N))
    (hSp : ∀ {N : ℕ} {lambda : ℝ} {H0 : CEH.SourceHermitian N},
      4 ≤ N → 0 < lambda → ∀ M : CEH.MDEBranch lambda H0, Nonempty (CEH.TypicalSpacing M))
    (hPre : BlockBand.External.Prekopa.SourceContract)
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
  smallCritical_of_layerContracts_psss hpsss hLp hMT hRing hRank hFresh w hc
    (fun _ _ _ hb hb' hθ _ =>
      BlockBand.QUE.GUEInputs.physicalAngularModeContract_of_gueInputs hEig hSp hPre hMDE hETH hELG hLp hPBC
        hMT hRank hC hP hD hPole hBridge hComp hb hb' hθ w hw)

end BlockBand.Internal.ReducedInputs
