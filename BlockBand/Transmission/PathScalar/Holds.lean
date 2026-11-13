module

public import BlockBand.Transmission.PathScalar.AbsorbedStart
public import BlockBand.Transmission.PathScalar.All
public import BlockBand.Transmission.PathScalar.RowBound

/-!
# `PassiveInitialScalarContract` from the passive one-port step

`passiveInitialScalar_holds`: `PassiveInitialScalarContract` from the hypotheses
`MatchedTracesContract`,
* `PassiveLayer.PassiveBoundsStatement` (only its `moments` field is used: the
  lead-augmented layer resolvent at `w = z_∂`, for the absorption shift at the first length);
* `PassiveMeanStep` and `PassiveFluctuationStep` (the passive one-port scalar step), proved by
  `passiveMeanStep_holds` and `PassiveLayer.passiveFluctuationStep_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer

/-- **The absorbed clause** `AbsorbedMomentClause` from `MatchedTracesContract`,
`PassiveBoundsStatement` and the passive one-port mean and fluctuation steps. -/
theorem absorbedMoment_of_passiveSteps (hMT : MatchedTracesContract)
    (hPB : PassiveBoundsStatement) (hMean : PassiveMeanStep) (hFl : PassiveFluctuationStep) :
    AbsorbedMomentClause :=
  absorbedMoment_of_steps hMean hFl (absorbedStartBound_holds hMT hPB)

/-- **The passive initial scalar lemma** (all three fields), from the passive one-port step
(`PassiveMeanStep`, `PassiveFluctuationStep`), `MatchedTracesContract` and
`PassiveBoundsStatement`. -/
theorem passiveInitialScalar_holds (hMT : MatchedTracesContract) (hPB : PassiveBoundsStatement)
    (hMean : PassiveMeanStep) (hFl : PassiveFluctuationStep) : PassiveInitialScalarContract :=
  passiveInitialScalar_of_absorbed hMT (absorbedMoment_of_passiveSteps hMT hPB hMean hFl)

end BlockBand.Transmission.PathScalar
