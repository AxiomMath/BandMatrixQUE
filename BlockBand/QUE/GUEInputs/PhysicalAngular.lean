module

public import BlockBand.QUE.Assembly.PhysicalAngularComplete
public import BlockBand.QUE.GUEInputs.PartTwoHolds

/-!
# The physical angular theorem from the GUE-scope inputs

`physicalAngularModeContract_of_gueInputs`: the statement of `physicalAngularModeContract_holds`
with `NativeInputs` replaced by the following hypotheses, besides the external and internal
statements taken as hypotheses there: the types of the deterministic fields `eigenpairs_exist`
and `spacing_exists` (hypotheses hEig and hSp), the Prékopa source contract
`Prekopa.SourceContract`, and the two law-bridge statements `PairGUELawBridgeStatement` and
`CompressedGUELawBridgeStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.GUEInputs

open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.External BlockBand.LocalWindow.LawBridge

/-- **The physical angular theorem** (`QUE.PhysicalAngularModeContract`, at `φ = conj A_m`), for
every Dyson centre family and `0 < θ`, from the deterministic fields `eigenpairs_exist` and
`spacing_exists` (in place of `NativeInputs`) and the two law-bridge statements. -/
theorem physicalAngularModeContract_of_gueInputs
    (hEig : ∀ (N : ℕ), 0 < N → Nonempty (CEH.EigenpairSelection N))
    (hSp : ∀ {N : ℕ} {lambda : ℝ} {H0 : CEH.SourceHermitian N},
      4 ≤ N → 0 < lambda → ∀ M : CEH.MDEBranch lambda H0, Nonempty (CEH.TypicalSpacing M))
    (hPre : BlockBand.External.Prekopa.SourceContract)
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
    (BlockBand.LocalWindow.GUEInputs.physicalLocalWindow_holds hEig hSp hMDE hETH hELG hPBC hMT
      hRank hC hBridge hComp) hb hb' hθ w hw

end BlockBand.QUE.GUEInputs
