module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubRes
public import BlockBand.SourceProcess.PhysApprox.B3BirthMFar

/-!
# The far birth masses from the contract hypotheses

Under `MatchedTracesContract` and `GaussianAbsorptionContract`, the newborn far mass
`NewbornFarMass` holds, hence `BirthKFarIn` and `BirthKFarOut`; with the path-only resolvent
estimates `BirthKResInPath`, `BirthKResOutPath` this gives `ComplexBirthKClosing`
(`complexBirthKClosing_of_contracts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthKSub

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs

theorem newbornFarMass_of_contracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) : NewbornFarMass :=
  BirthM.newbornFarMass_holds hMT hGA

/-- **`BirthKFarIn` holds** under `MatchedTracesContract` and `GaussianAbsorptionContract`. -/
theorem birthKFarIn_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) :
    BirthKFarIn :=
  birthKFarIn_of_mass (newbornFarMass_of_contracts hMT hGA)

/-- **`BirthKFarOut` holds** under `MatchedTracesContract` and `GaussianAbsorptionContract`. -/
theorem birthKFarOut_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) :
    BirthKFarOut :=
  birthKFarOut_of_mass (newbornFarMass_of_contracts hMT hGA)

/-- **`ComplexBirthKClosing`** from `MatchedTracesContract`, `GaussianAbsorptionContract` and the
two path-only resolvent hypotheses `BirthKResInPath`, `BirthKResOutPath`. -/
theorem complexBirthKClosing_of_contracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hRI : BirthKResInPath) (hRO : BirthKResOutPath) :
    ComplexBirthKClosing :=
  complexBirthKClosing_of_parts (birthKFarIn_holds hMT hGA) (birthKFarOut_holds hMT hGA)
    (birthKResIn_of_path hRI) (birthKResOut_of_path hRO)

end BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
