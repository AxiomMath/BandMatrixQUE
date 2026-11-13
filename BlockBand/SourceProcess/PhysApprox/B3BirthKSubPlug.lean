module

public import BlockBand.SourceProcess.PhysApprox.B3GramStepBirth
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubDiag

/-!
# `GenReqBirth` without `ComplexBirthKClosing`

**`genReqBirth_of_closedBirth_jet`**: `GenReqBirth` with `ComplexBirthKDiag` discharged by
`complexBirthKDiag_of_jet hGA hLp hJ`; the other hypotheses are the input hypotheses,
`KCorrStepFourAt`, `ClosedGramStepFourSmall`, `ComplexBirthGramDiag` and `ClosedJet0Fam` (used at
`p = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs

/-- **`GenReqBirth` from the closed-path birth estimates** (no `ComplexBirthKClosing`). -/
theorem genReqBirth_of_closedBirth (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hC : KCorrStepFourAt) (hG : ClosedGramStepFourSmall)
    (hGd : ComplexBirthGramDiag) (hKD : ComplexBirthKDiag) : GenReqBirth :=
  genReqBirth_of_parts (complexBirthOld_of_small hGA hLp hSR hMT hC hG) hGd hKD
    (complexBirthCross_of_parts (complexBirthCrossGram_of_small hMT hGA hG)
      (complexBirthCrossK_holds hGA))

/-- `genReqBirth_of_closedBirth` with `ComplexBirthCrossK` as an explicit hypothesis. -/
theorem genReqBirth_of_closedBirth' (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hC : KCorrStepFourAt) (hG : ClosedGramStepFourSmall)
    (hGd : ComplexBirthGramDiag) (hKD : ComplexBirthKDiag) (hKX : ComplexBirthCrossK) :
    GenReqBirth :=
  genReqBirth_of_parts (complexBirthOld_of_small hGA hLp hSR hMT hC hG) hGd hKD
    (complexBirthCross_of_parts (complexBirthCrossGram_of_small hMT hGA hG) hKX)

/-- **`GenReqBirth` from the input hypotheses, `KCorrStepFourAt`, `ClosedGramStepFourSmall`,
`ComplexBirthGramDiag` and the closed jet `ClosedJet0Fam`** (no `ComplexBirthKClosing`). -/
theorem genReqBirth_of_closedBirth_jet (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hC : KCorrStepFourAt) (hG : ClosedGramStepFourSmall)
    (hGd : ComplexBirthGramDiag) (hJ : ClosedJet0Fam) : GenReqBirth :=
  genReqBirth_of_closedBirth hMT hGA hLp hSR hC hG hGd (complexBirthKDiag_of_jet hGA hLp hJ)

end BlockBand.SourceProcess.PhysApprox.B3
