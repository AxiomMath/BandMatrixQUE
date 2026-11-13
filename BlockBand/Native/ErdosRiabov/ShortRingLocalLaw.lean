module

public import BlockBand.Native.ErdosRiabov.SatLin.Gain

/-!
# The short-ring local law from the Erdős–Riabov proof

`shortRingLocalLaw_holds` proves `Inputs.ShortRingLocalLaw` with no hypotheses, through
`SatLin.shortRingLocalLaw_of_satLin`. The chain uses results proved in other modules:

* `SatLin.masterIneqSat`: `MI.MasterIneqSat`, the saturated averaged master inequalities;
* `MI.masterIneqPhi_of_MI`: all master inequalities, `ZigProof.MasterIneqPhi`;
* `ZigProof.shortRingLocalLaw_of_masterIneqPhi`: the zig bootstrap and the extraction
  `Assembly.shortRingLocalLaw_of_zig`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Native.ErdosRiabov

/-- **The short-ring local law** `Inputs.ShortRingLocalLaw` (the external band local law of
Erdős–Riabov for the short ring), proved with no hypotheses.
-/
theorem shortRingLocalLaw_holds : BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  SatLin.shortRingLocalLaw_of_satLin

end BlockBand.Native.ErdosRiabov
