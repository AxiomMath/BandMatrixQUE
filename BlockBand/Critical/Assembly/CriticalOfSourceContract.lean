module

public import BlockBand.Critical.Assembly.CriticalOfRelativeVectors
public import BlockBand.Critical.GlobalSource.FromSequences

/-!
# The critical theorem from the sequence form of the complex source law

The hypothesis `ComplexSourceLimitAlongSequences` of `critical_of_relativeVectors` is supplied by
`GlobalSource.complexSourceLimitAlongSequences_of_contract` from
`TransmissionSequences.ComplexSourceLimitSequenceContract`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Assembly

open MeasureTheory BlockBand.Internal.Contracts

/-- The critical theorem, conditional on `RelativeMixedVectorsStatement`,
`ComplexSourceLimitSequenceContract` and the listed inputs. -/
theorem critical_of_relativeVectors_sourceContract
    (hRMV : BlockBand.Critical.RelativeVectors.RelativeMixedVectorsStatement)
    (hSeq : TransmissionSequences.ComplexSourceLimitSequenceContract)
    (hCS : TransmissionLaws.ComplexSourceLawContract)
    (hP : CoareaPalm.FreshPalmContract)
    (hTM : Layers.TraceMatrixContract) (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hLC : Layers.LayerComparisonContract)
    (hES : Inputs.ExternalSine) (hUI : Inputs.CriticalUnitIntensity)
    (hS : Inputs.CriticalStationarity)
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family :=
  critical_of_relativeVectors hRMV
    (BlockBand.Critical.GlobalSource.complexSourceLimitAlongSequences_of_contract hSeq)
    hCS hP hTM hMT hGA hLC hES hUI hS source b E hb hb' hE

end BlockBand.Critical.Assembly
