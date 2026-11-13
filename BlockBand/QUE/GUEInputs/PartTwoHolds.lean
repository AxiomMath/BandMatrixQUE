module

public import BlockBand.LocalWindow.ProofPartTwoHolds
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoLargeAssembly
public import BlockBand.QUE.GUEInputs.PartTwoSmall

/-!
# The physical local window lemma (GUE inputs)

Part (ii) of the physical local window lemma (`physicalLocalWindow_partTwo`) and the lemma itself,
parts (i) and (ii) (`physicalLocalWindow_holds`).

The statements are those of `BlockBand.LocalWindow.ProofPartTwoHolds`, with `NativeInputs` replaced
by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of `External.CEH.SourceContract`) as
needed, and without `GUEWignerFamilyAdapter`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.GUEInputs

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.LocalWindow.LawBridge

/-- **The physical local window lemma, part (ii).** -/
theorem physicalLocalWindow_partTwo (hEig : BlockBand.QUE.GUEInputs.EigenpairsExist) (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalLocalWindowPartTwoStatement :=
  ProofPartTwo.physicalLocalWindow_partTwo_of_branches
    (BlockBand.LocalWindow.ProofPartTwo.GUEInputs.partTwoSmallRho_holds hEig hSp hMDE hETH hELG hPBC hMT hRL hCo hBridge)
    (BlockBand.LocalWindow.ProofPartTwo.GUEInputs.partTwoLargeRho_holds hEig hSp hMDE hETH hELG hPBC hMT hRL hCo hBridge hComp)

/-- **The physical local window lemma**, parts (i) and (ii). -/
theorem physicalLocalWindow_holds (hEig : BlockBand.QUE.GUEInputs.EigenpairsExist) (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : ProofPartTwo.CompressedGUELawBridgeStatement) :
    PhysicalLocalWindowStatement :=
  physicalLocalWindow_of_parts (physicalLocalWindow_partOne hBridge hELG hMDE hPBC hMT hRL hCo)
    (BlockBand.LocalWindow.GUEInputs.physicalLocalWindow_partTwo hEig hSp hMDE hETH hELG hPBC hMT hRL hCo hBridge hComp)

end BlockBand.LocalWindow.GUEInputs
