module

public import BlockBand.SourceProcess.ComplexUnique.Holds
public import BlockBand.SourceProcess.ComplexUniqueSegment.Main
public import BlockBand.SourceProcess.ComplexSourceLaw.Assembly
public import BlockBand.SourceProcess.ComplexSourceLaw.Extended
public import BlockBand.SourceProcess.RawTag.Holds

/-!
# `ComplexFiniteUniqueness` with no hypotheses

* `complexFiniteUniqueness_holds`: `ComplexFiniteUniqueness`, from the joint segment law
  `ComplexUnique.jointSegmentLaw_holds` and concatenation over the births.
* `complexSourceLawContract_of_construction`: `ComplexSourceLawContract` from the Gaussian,
  scalar-recursion and matched-traces inputs and `ComplexSourceConstruction`; `moments` and
  `rawTagMoments` come from `RawTag.rawTagMoments_holds`, and `extendedSourceMoments` from
  `extendedSourceMoments_of_raw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSplit

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **`ComplexFiniteUniqueness`**, with no hypotheses. -/
theorem complexFiniteUniqueness_holds : ComplexFiniteUniqueness :=
  ComplexUniqueSegment.complexFiniteUniqueness_of_segment ComplexUnique.jointSegmentLaw_holds

/-- **The `ComplexSourceLawContract`** from the input hypotheses and the open
`ComplexSourceConstruction`.
-/
theorem complexSourceLawContract_of_construction (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : ComplexSourceConstruction) : ComplexSourceLawContract :=
  complexSourceLawContract_of complexFiniteUniqueness_holds hC
    (RawTag.rawTagMoments_holds hGA hLp hSR hMT)
    (extendedSourceMoments_of_raw (RawTag.rawTagMoments_holds hGA hLp hSR hMT))

end BlockBand.SourceProcess.ComplexSplit
