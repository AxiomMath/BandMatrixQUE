module

public import BlockBand.Transmission.SourceMixing.Conductance
public import BlockBand.Transmission.SourceMixing.Mixing
public import BlockBand.Transmission.SourceMixing.MeanAll

/-!
# The passive source-mixing lemma

`passiveSourceMixing_holds` proves `PassiveSourceMixingContract` from the matched-traces, Gaussian
absorption and Gaussian `L^p`-gradient inputs (`MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient`). The four fields of the structure come from:

* the field `mixing`: `mixing_of_mass`, with the mass moment bound `massMomentBound_holds`;
* the field `finiteConductance`: `conductanceMomentBound_holds`;
* the field `oneStepMean`: `oneStepMean_holds` applied to `passiveBounds_holds`;
* the field `oneStepFluctuation`: `oneStepFluctuation_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs

/-- , from the input hypotheses. -/
theorem passiveSourceMixing_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    PassiveSourceMixingContract where
  mixing := mixing_of_mass hMT hGA hLp fun _ hb0 hb _ h1 h2 =>
    massMomentBound_holds hMT hGA hLp hb0 hb h1 h2
  finiteConductance := conductanceMomentBound_holds hMT hGA hLp
  oneStepMean := oneStepMean_holds (PassiveLayer.passiveBounds_holds hGA hLp)
  oneStepFluctuation := oneStepFluctuation_holds hGA hLp

end BlockBand.Transmission.SourceMixing
