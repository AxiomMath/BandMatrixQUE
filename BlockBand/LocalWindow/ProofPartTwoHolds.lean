module

public import BlockBand.LocalWindow.ProofPartTwoSmall
public import BlockBand.LocalWindow.ProofPartTwoLargeAssembly
public import BlockBand.LocalWindow.ProofPartOne

/-!
# The physical local window

Proof of part (ii) of the physical local-window lemma and of the full statement.

## Main results

* `physicalLocalWindow_partTwo`: `PhysicalLocalWindowPartTwoStatement` from the reduction
  `ProofPartTwo.physicalLocalWindow_partTwo_of_branches` (split on `σ = ‖F(E) − truncF(E)‖`), the
  small-`ρ` branch `ProofPartTwo.partTwoSmallRho_holds` and the large-`ρ` branch
  `ProofPartTwo.partTwoLargeRho_holds`.
* `physicalLocalWindow_holds`: `PhysicalLocalWindowStatement` from part (i)
  (`physicalLocalWindow_partOne`) and part (ii) via `physicalLocalWindow_of_parts`.

The hypotheses are `NativeInputs`, `GUEWignerFamilyAdapter`, `MDEBranchIdentification`,
`ExternalETH`, `ExternalLocalGUE`, `PhysicalBlockConditionalCount`, `MatchedTracesContract`,
`RankLocationContract`, `CoareaContract`, `PairGUELawBridgeStatement` and
`ProofPartTwo.CompressedGUELawBridgeStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.LocalWindow.LawBridge

/-- **Part (ii) of the physical local window.** -/
theorem physicalLocalWindow_partTwo (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalLocalWindowPartTwoStatement :=
  ProofPartTwo.physicalLocalWindow_partTwo_of_branches
    (ProofPartTwo.partTwoSmallRho_holds inputs hAd hMDE hETH hELG hPBC hMT hRL hCo hBridge)
    (ProofPartTwo.partTwoLargeRho_holds inputs hAd hMDE hETH hELG hPBC hMT hRL hCo hBridge hComp)

/-- **The physical local window**, parts (i) and (ii). -/
theorem physicalLocalWindow_holds (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalLocalWindowStatement :=
  physicalLocalWindow_of_parts (physicalLocalWindow_partOne hBridge hELG hMDE hPBC hMT hRL hCo)
    (physicalLocalWindow_partTwo inputs hAd hMDE hETH hELG hPBC hMT hRL hCo hBridge hComp)

end BlockBand.LocalWindow
