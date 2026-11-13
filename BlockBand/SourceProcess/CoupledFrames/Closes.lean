module

public import BlockBand.SourceProcess.CoupledFrames.Result
public import BlockBand.SourceProcess.CutoffLimit.Main

/-!
# Removal of the cutoff

`cutoffRemoval_of_baseContracts`: the cutoff-removal statement `CutoffRemoval` holds under the matched
traces, Gaussian absorption, Gaussian `L^p` gradient and Gaussian Poincaré hypotheses, using the
coupled cutoff frames `coupledCutoffFrames_holds`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.CutoffLimit BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs

/-- **`CutoffRemoval`** from `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`
and `GaussianPoincare`, with the coupled cutoff models `coupledCutoffFrames_holds`. -/
theorem cutoffRemoval_of_baseContracts (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : CutoffRemoval :=
  cutoffRemoval_holds hMT hGA hLp hP coupledCutoffFrames_holds

end BlockBand.SourceProcess.CoupledFrames
