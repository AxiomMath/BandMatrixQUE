module

public import BlockBand.SourceProcess.SourcePins.FreqAssembly
public import BlockBand.SourceProcess.SourcePins.AtomLimit
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction
public import BlockBand.SourceProcess.SourceProcessLaw.EarlyMain

/-!
# The source process theorem from the model, removal, sampling and approximation hypotheses

`sourceProcessContract_of_pins'` derives `SourceProcessContract` (the source process theorem) from
the matched-traces, Gaussian layer and scalar recursion hypotheses, the model, cap-removal and
cutoff-removal hypotheses, `PhysicalSamplingWeak`, `PhysicalApproximationFreq` and
`RankFreeCoupling`. The transmission law, `EntranceAtomic`, `SeqExtraction` (`seqExtraction_holds`)
and the early sources are supplied by proved results.

`sourceProcessContract_of_sp1Pins` is the same theorem with the stronger `PhysicalSampling` and
`PhysicalApproximation`. Several of these hypotheses are proved elsewhere, for instance
`ModelExist.modelExists_holds`, `ClosedIdent.modelUnique_holds`, `RankFree.rankFreeCoupling_holds`
and `Sampling.physicalSamplingWeak_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw

/-- **The source process theorem** `SourceProcessContract` from the input hypotheses and
`ModelExists`, `ModelUnique`, `CapRemoval`, `CutoffRemoval`, `PhysicalSamplingWeak`,
`PhysicalApproximationFreq`, `RankFreeCoupling`.
-/
theorem sourceProcessContract_of_pins' (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hB1 : ModelExists) (hB2 : ModelUnique) (hC : CapRemoval)
    (hD : CutoffRemoval) (hE1 : PhysicalSamplingWeak) (hE2 : PhysicalApproximationFreq)
    (hRF : RankFreeCoupling) : SourceProcessContract :=
  have hTL := Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP
  sourceProcessContract_of_freq hTL (entranceAtomic_of hTL) seqExtraction_holds hB1 hB2 hC hD
    hE1 hE2 (earlySources_holds hGA hLp hSR) hRF

/-- The same with the stronger `PhysicalSampling` and `PhysicalApproximation`. -/
theorem sourceProcessContract_of_sp1Pins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hB1 : ModelExists) (hB2 : ModelUnique) (hC : CapRemoval)
    (hD : CutoffRemoval) (hE1 : PhysicalSampling) (hE2 : PhysicalApproximation)
    (hRF : RankFreeCoupling) : SourceProcessContract :=
  sourceProcessContract_of_pins' hMT hGA hLp hP hSR hB1 hB2 hC hD (physicalSamplingWeak_of hE1)
    (physicalApproximationFreq_of hE2) hRF

end BlockBand.SourceProcess.SourcePins
