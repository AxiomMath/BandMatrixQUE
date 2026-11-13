module

public import BlockBand.SourceProcess.FullSource.EstimatesHolds
public import BlockBand.SourceProcess.FullSource.DeltaFlucHolds
public import BlockBand.SourceProcess.FullSource.DeltaMeanHolds

/-!
# The full-source estimates and moments

The fluctuation and mean bounds for `Δ` (`deltaFluctuation_holds`, `deltaMean_holds`) give the
full-source estimates `FullSourceEstimates`, the full-source moment bounds, the edge clock moments
and the bulk clock square bound, under the Gaussian absorption, Gaussian `L^p` gradient and
scalar recursion hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs

/-- **`FullSourceEstimates`** from `GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem fullSourceEstimates_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    FullSourceEstimates :=
  fullSourceEstimates_of_delta hGA (deltaFluctuation_holds hGA hLp) (deltaMean_holds hGA hLp)

/-- **`FullSourceMomentsContract`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`ScalarRecursionContract`. -/
theorem fullSourceMoments_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : FullSourceMomentsContract :=
  fullSourceMoments_of_delta hGA hLp hSR (deltaFluctuation_holds hGA hLp) (deltaMean_holds hGA hLp)

/-- **`EdgeClockMomentsContract`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`ScalarRecursionContract`. -/
theorem edgeClockMoments_holds' (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : EdgeClockMomentsContract :=
  edgeClockMoments_of_delta hGA hLp hSR (deltaFluctuation_holds hGA hLp) (deltaMean_holds hGA hLp)

/-- `ClockSquareBulk` from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`ScalarRecursionContract`. -/
theorem clockSquareBulk_holds' (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : ClockSquareBulk :=
  clockSquareBulk_of_delta hGA hLp hSR (deltaFluctuation_holds hGA hLp) (deltaMean_holds hGA hLp)

end BlockBand.SourceProcess.FullSource
