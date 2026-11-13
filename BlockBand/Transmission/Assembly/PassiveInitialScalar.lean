module

public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PassiveLayer.FlucMain
public import BlockBand.Transmission.PassiveLayer.Assembly
public import BlockBand.Transmission.PassiveLayer.TMMain

set_option autoImplicit false

@[expose] public section
noncomputable section

/-!
# The passive initial scalar bound

`passiveInitialScalar_holds`: `PassiveInitialScalarContract` follows from the matched-traces and
Gaussian layer hypotheses, through the trace-matrix clause (`passiveInitialScalar_of_traceMatrix`)
and the passive fluctuation step.
-/

namespace BlockBand.Transmission.Assembly
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionStatements

/-- **`PassiveInitialScalarContract` from the input hypotheses and the trace-matrix clause
`PassiveLayer.TraceMatrixClause`.**
-/
theorem passiveInitialScalar_of_traceMatrix (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (htr : PassiveLayer.TraceMatrixClause) : PassiveInitialScalarContract :=
  PathScalar.passiveInitialScalar_holds_of_fluctuation hMT
    (PassiveLayer.passiveBounds_of_traceMatrix hGA hLp htr)
    (PassiveLayer.passiveFluctuationStep_holds hGA hLp)

/-- **`PassiveInitialScalarContract` from the input hypotheses only:** `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem passiveInitialScalar_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : PassiveInitialScalarContract :=
  passiveInitialScalar_of_traceMatrix hMT hGA hLp (PassiveLayer.traceMatrix_holds hGA)

end BlockBand.Transmission.Assembly
