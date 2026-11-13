module

public import BlockBand.Transmission.PathScalar.Holds
public import BlockBand.Transmission.PathScalar.MeanStep

/-!
# `PassiveInitialScalarContract` with the mean step reduced to the mean equations

`passiveInitialScalar_holds_of_equations`: the passive initial scalar lemma from
`MatchedTracesContract`, `PassiveBoundsStatement`, the one-port mean equations
`PassiveMeanEquations` and the fluctuation step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer

theorem passiveInitialScalar_holds_of_equations (hMT : MatchedTracesContract)
    (hPB : PassiveBoundsStatement) (hEq : PassiveMeanEquations) (hFl : PassiveFluctuationStep) :
    PassiveInitialScalarContract :=
  passiveInitialScalar_holds hMT hPB (passiveMeanStep_of_equations hEq) hFl

end BlockBand.Transmission.PathScalar
