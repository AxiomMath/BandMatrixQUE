module

public import BlockBand.Critical.Assembly.CriticalOfEntireLaw
public import BlockBand.Critical.EntireLaw.ClosedSourceStep
public import BlockBand.Critical.MatrixClosing.Poles.GoodEvent
public import BlockBand.Critical.GlobalSource
public import BlockBand.Critical.PointDensity
public import BlockBand.Critical.CommonPort

/-!
# The critical theorem from the relative mixed vectors theorem

The critical theorem follows from `RelativeMixedVectorsStatement` by composing

* `GlobalSource.globalGaussianSource_holds_of_sourceLimit` (the global Gaussian source lemma);
* `MatrixClosing.Poles.matrixClosing_of_relativeVectors` (the matrix closing theorem);
* `EntireLaw.entireLaw_of_matrixClosing` (the entire-law theorem);
* `Assembly.critical_of_entireLaw` (joint recovery and the critical theorem);
* `PointDensity.pointDensity_holds` and `CommonPort.commonPortMean_holds`.

The other hypotheses are those listed in `critical_of_relativeVectors`, including the external
Peled–Schenker–Shamis–Sodin (PSSS) input `BlockBand.External.PSSS.SourceContract.{0}`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Assembly

open MeasureTheory BlockBand.Internal.Contracts

/-- The critical theorem, conditional on `RelativeMixedVectorsStatement`,
`ComplexSourceLimitAlongSequences` and the listed inputs. -/
theorem critical_of_relativeVectors
    (hRMV : BlockBand.Critical.RelativeVectors.RelativeMixedVectorsStatement)
    (hA : BlockBand.Critical.GlobalSource.ComplexSourceLimitAlongSequences)
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
  critical_of_entireLaw
    (BlockBand.Critical.EntireLaw.entireLaw_of_matrixClosing
      (BlockBand.Critical.GlobalSource.globalGaussianSource_holds_of_sourceLimit hCS hA)
      (BlockBand.Critical.MatrixClosing.Poles.matrixClosing_of_relativeVectors hRMV hP
        (BlockBand.Critical.PointDensity.pointDensity_holds hES)
        (BlockBand.Critical.CommonPort.commonPortMean_holds hGA hLC) hTM source)
      source hMT)
    source hUI hS b E hb hb' hE

end BlockBand.Critical.Assembly
