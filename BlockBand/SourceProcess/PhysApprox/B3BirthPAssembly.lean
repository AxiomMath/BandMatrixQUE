module

public import BlockBand.SourceProcess.PhysApprox.B3BirthAssembly
public import BlockBand.SourceProcess.PhysApprox.B3BirthPCross

/-!
# `GenReqBirth` from four birth estimates

`genReqBirth_of_baseContracts`: under the contract hypotheses, the birth half `GenReqBirth` of the generator
estimates follows from `ComplexBirthOldL2`, `ComplexBirthGramDiag`, `ComplexBirthKClosing` and
`ComplexBirthCrossGram`; the other two, `ComplexBirthKFreshTrace` and `ComplexBirthKFreshCross`, are
proved as `complexBirthKFreshTrace_holds` and `complexBirthKFreshCross_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-- **The birth half `GenReqBirth` from the input hypotheses and four birth estimates.** -/
theorem genReqBirth_of_baseContracts (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hO : ComplexBirthOldL2)
    (hG : ComplexBirthGramDiag) (hC : ComplexBirthKClosing) (hGX : ComplexBirthCrossGram) :
    GenReqBirth :=
  genReqBirth_of_pins hO hG (complexBirthKFreshTrace_holds hMT hGA hLp)
    (complexBirthKFreshCross_holds hGA hLp hSR) hC hGX

end BlockBand.SourceProcess.PhysApprox.B3
