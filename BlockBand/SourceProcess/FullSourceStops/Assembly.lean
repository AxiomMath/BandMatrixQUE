module

public import BlockBand.SourceProcess.FullSourceStops.Main
public import BlockBand.SourceProcess.FullSourceStops.CoefficientMoments
public import BlockBand.SourceProcess.FullSourceStops.FractionalUniform

/-!
# The full-source stops lemma from the current tail

The current tail bound `CurrentNuclearTail` and the compensator coefficient moments give the
energy-uniform full-source stops statement and its fixed-energy form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform2

/-- **The energy-uniform contract** from input hypotheses and `CurrentNuclearTail`. -/
theorem fullSourceStopsEnergyUniform_holds_of_current (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hJ : CurrentNuclearTail) :
    FullSourceStopsEnergyUniformContract :=
  fullSourceStopsEnergyUniform_of hGA hLp hSR hJ
    (compensatorCoefficientMoments_holds hMT hGA hLp hSR)

/-- **The `FullSourceStopsContract`** from input hypotheses and `CurrentNuclearTail`. -/
theorem fullSourceStops_holds_of_current (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hJ : CurrentNuclearTail) : FullSourceStopsContract :=
  fullSourceStops_of_uniform (fullSourceStopsEnergyUniform_holds_of_current hMT hGA hLp hSR hJ)

end BlockBand.SourceProcess.FullSourceStops
