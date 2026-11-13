module

public import BlockBand.SourceProcess.ComplexFreq.Assembly
public import BlockBand.SourceProcess.ComplexCutoff.Holds
public import BlockBand.SourceProcess.BracketDef.Bridge

/-!
# `ComplexSourceLawContract` without `BornKExtension`

`complexSourceLawContract_of_coupled`: `ComplexSourceLawContract` from the matched-traces, Gaussian
and scalar-recursion inputs, `CoupledComplexCutoff`, `StoppedBracketCoupling` and
`ComplexPhysicalApproximationFreq`. The model existence step comes from the coupling
(`complexModelExists_of_coupled`) instead of `BornKExtension`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexFreq

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct

/-- **The `ComplexSourceLawContract`** from the input hypotheses, `CoupledComplexCutoff`,
`StoppedBracketCoupling` and `ComplexPhysicalApproximationFreq`.
-/
theorem complexSourceLawContract_of_coupled (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hA : ComplexCutoff.CoupledComplexCutoff)
    (hS : BracketDef.StoppedBracketCoupling) (hPA : ComplexPhysicalApproximationFreq) :
    ComplexSourceLawContract :=
  ComplexSplit.complexSourceLawContract_of_construction hGA hLp hSR hMT
    (complexSourceConstruction_of_pins_freq
      (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
      (BlockBand.SourceProcess.SourcePins.entranceAtomic_holds hMT hGA hLp hP)
      BlockBand.SourceProcess.SourceProcessLaw.seqExtraction_holds
      ComplexSplit.complexFiniteUniqueness_holds
      (ComplexCutoff.complexModelExists_of_coupled hA) ComplexSplit.complexCapRemoval_holds
      (ComplexCutoff.complexCutoffRemoval_holds' hMT hGA hLp hP hA
        (BracketDef.stoppedBracketCoupling_of hS)) hPA
      (complexSourceTight_of_raw (RawTag.rawTagMoments_holds hGA hLp hSR hMT)))

end BlockBand.SourceProcess.ComplexFreq
