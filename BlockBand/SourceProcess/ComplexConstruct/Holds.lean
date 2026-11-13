module

public import BlockBand.SourceProcess.ComplexConstruct.Assembly
public import BlockBand.SourceProcess.ComplexConstruct.Model
public import BlockBand.SourceProcess.ComplexSplit.Holds
public import BlockBand.SourceProcess.SourcePins.AtomLimit
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction

/-!
# `ComplexSourceConstruction` and `ComplexSourceLawContract` from the inputs and the named steps

* `complexSourceConstruction_of`: `ComplexSourceConstruction` from the matched-traces, Gaussian and
  scalar-recursion inputs and the steps `ComplexModelExists`, `ComplexCapRemoval`,
  `ComplexCutoffRemoval`, `ComplexPhysicalApproximation`, taken as hypotheses here
  (`ComplexModelExists` and `ComplexCapRemoval` are proved as
  `ComplexCoupled.complexModelExists_holds'` and `ComplexSplit.complexCapRemoval_holds`).
* `complexSourceLawContract_of_pins`: the same for `ComplexSourceLawContract`.
* `complexSourceLawContract_of_kExt`: the same with `ComplexModelExists` replaced by
  `BornKExtension` (`complexModelExists_of_kExtension`, the Gram part being proved).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **`ComplexSourceConstruction`** from the input hypotheses and the four hypotheses
`ComplexModelExists`, `ComplexCapRemoval`, `ComplexCutoffRemoval`,
`ComplexPhysicalApproximation`. -/
theorem complexSourceConstruction_of (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hEx : ComplexModelExists) (hCap : ComplexCapRemoval)
    (hCut : ComplexCutoffRemoval) (hPA : ComplexPhysicalApproximation) :
    ComplexSourceConstruction :=
  complexSourceConstruction_of_pins
    (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
    (BlockBand.SourceProcess.SourcePins.entranceAtomic_holds hMT hGA hLp hP)
    BlockBand.SourceProcess.SourceProcessLaw.seqExtraction_holds
    ComplexSplit.complexFiniteUniqueness_holds hEx hCap hCut hPA
    (complexSourceTight_of_raw (RawTag.rawTagMoments_holds hGA hLp hSR hMT))

/-- **The `ComplexSourceLawContract`** from the input hypotheses and the same four hypotheses. -/
theorem complexSourceLawContract_of_pins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hEx : ComplexModelExists) (hCap : ComplexCapRemoval)
    (hCut : ComplexCutoffRemoval) (hPA : ComplexPhysicalApproximation) :
    ComplexSourceLawContract :=
  ComplexSplit.complexSourceLawContract_of_construction hGA hLp hSR hMT
    (complexSourceConstruction_of hMT hGA hLp hP hSR hEx hCap hCut hPA)

/-- **The `ComplexSourceLawContract`** from the input hypotheses, the `𝒦`-extension
`BornKExtension` and the three hypotheses `ComplexCapRemoval`, `ComplexCutoffRemoval`,
`ComplexPhysicalApproximation`.
-/
theorem complexSourceLawContract_of_kExt (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hK : BornKExtension) (hCap : ComplexCapRemoval)
    (hCut : ComplexCutoffRemoval) (hPA : ComplexPhysicalApproximation) :
    ComplexSourceLawContract :=
  complexSourceLawContract_of_pins hMT hGA hLp hP hSR (complexModelExists_of_kExtension hK) hCap
    hCut hPA

end BlockBand.SourceProcess.ComplexConstruct
