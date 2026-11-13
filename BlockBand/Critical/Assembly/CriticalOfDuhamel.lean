module

public import BlockBand.Critical.Assembly.CriticalOfSourceContract
public import BlockBand.Critical.RelativeVectors.ComparisonStatement

/-!
# The critical theorem from the relative Duhamel and reference-flow statements

The critical theorem follows by composition: `RelativeMixedVectorsStatement` is obtained from
the relative Duhamel statement `RelativeDuhamelStatement`, the reference-flow statement
`ReferenceFlowStatement` and the other hypotheses by
`RelativeVectors.relativeMixedVectorsStatement_of_inputs`, and is then passed to
`critical_of_relativeVectors_sourceContract`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Assembly

open MeasureTheory BlockBand.Internal.Contracts

/-- The critical theorem, conditional on the relative Duhamel and reference-flow
statements and the listed inputs. -/
theorem critical_of_duhamel
    (hD : ∀ N r, BlockBand.Critical.RelativeVectors.RelativeDuhamelStatement N r)
    (hRF : ∀ N r, BlockBand.Critical.RelativeVectors.ReferenceFlowStatement N r)
    (hCR : CoareaPalm.CoarseRelativeContract) (hLp : Inputs.GaussianLpGradient)
    (hSG : CoareaPalm.SpectralGoodEventContract) (hRL : CoareaPalm.RelativeLocalizationContract)
    (hDBM : ∀ N, Transmission.DysonBrownianMotion N)
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
  critical_of_relativeVectors_sourceContract
    (BlockBand.Critical.RelativeVectors.relativeMixedVectorsStatement_of_inputs hD hRF hCR hLp hSG hRL hDBM
      source hES)
    hSeq hCS hP hTM hMT hGA hLC hES hUI hS source b E hb hb' hE

end BlockBand.Critical.Assembly
