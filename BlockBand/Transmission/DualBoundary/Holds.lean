module

public import BlockBand.Transmission.DualBoundary.LawAssembly
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# The boundary-start dual contract from the transmission inputs

`dualBoundaryStart_holds`: `DualBoundaryStartContract` holds given `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient` and `GaussianPoincare`. It composes
`dualBoundaryStart_of_transmissionLaw` with `LawForced.transmissionLawContract_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionUniform

/-- **The `DualBoundaryStartContract`**, from the input hypotheses. -/
theorem dualBoundaryStart_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : DualBoundaryStartContract :=
  dualBoundaryStart_of_transmissionLaw (LawForced.transmissionLawContract_holds hMT hGA hLp hP)

end BlockBand.Transmission.DualBoundary
