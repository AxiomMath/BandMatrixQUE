module

public import BlockBand.Endpoints.Response.RemoteHigherLimitGenerator
public import BlockBand.Endpoints.Response.RemoteHigherRecursion

/-!
# The remote higher-order clock theorem with the limit clause from a finite-width generator

`rhl_higherLimitDecay_of_onePort` derives `RhHigherLimitDecay` from the finite-width higher trace
generator `RhlFiniteTraceGenerator` and the one-port and transmission contracts, through the
higher recursion and the regularized limit generator. `remoteHigher_of_onePort'` then gives
`RemoteHigherStatement` with the limit clause supplied in this way.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.LayersOnePort

/-- **Higher clock decay at critical limits** (`RhHigherLimitDecay`) from the contracts in the
signature and the finite-width generator `RhlFiniteTraceGenerator`.
-/
theorem rhl_higherLimitDecay_of_onePort (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hJet : OnePortJetContraction)
    (hFin : RhlFiniteTraceGenerator) (hGen : FullSourceGeneratorContract) :
    RhHigherLimitDecay :=
  rhl_limitDecay
    (rhn_higherLater_of_recursion (rhnHigherWeightedRecursion_of_oneStep hECM hTLU
      (rhcHigherOneStep_of_onePort hCount hTL hPC hPSM hPM hOM hJet)))
    (rhl_regularizedLimitGenerator hFin hCount hGen.moments)

/-- **The remote higher-order theorem** (`RemoteHigherStatement`) from the contracts of
`remoteHigher_of_onePort`, with the finite-width `RhlFiniteTraceGenerator` in place of
`RhHigherLimitDecay`.
-/
theorem remoteHigher_of_onePort' (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hECM : EdgeClockMomentsContract) (hTLU : TransmissionLengthUniformContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hJet : OnePortJetContraction) (hFin : RhlFiniteTraceGenerator)
    (hGen : FullSourceGeneratorContract) : RemoteHigherStatement :=
  remoteHigher_of_onePort hCount hTL hPC hPSM hECM hTLU hPM hOM hJet
    (rhl_higherLimitDecay_of_onePort hCount hTL hPC hPSM hECM hTLU hPM hOM hJet hFin hGen) hGen

end BlockBand.Endpoints
