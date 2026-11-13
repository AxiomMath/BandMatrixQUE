module

public import BlockBand.Endpoints.Poisson.SingleCollarWard
public import BlockBand.Endpoints.Poisson.SingleCollarAssembly
public import BlockBand.Endpoints.Poisson.SingleCollarMoment

/-!
# The same-volume log-error bound from the component/path identification

`peSameVolumeLogError_of_componentPaths` derives `PeSameVolumeLogError` from the collar-kernel,
matched-traces, transmission-length and passive-log hypotheses, the uniform remote-higher
statement `RemoteHigherUniformStatement` and the component/path identification
`ScwComponentPaths`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.Layers (MatchedTracesContract)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open BlockBand.Internal.Contracts.Inputs (PassiveLog)

/-- **`PeSameVolumeLogError`**, from `CollarKernelContract`, `MatchedTracesContract`,
`TransmissionLengthUniformContract`, `PassiveLog`, `RemoteHigherUniformStatement` and
`ScwComponentPaths`.
-/
theorem peSameVolumeLogError_of_componentPaths (hK : CollarKernelContract)
    (hMT : MatchedTracesContract) (hTU : TransmissionLengthUniformContract) (hPL : PassiveLog)
    (hRHU : RemoteHigherUniformStatement) (hC : ScwComponentPaths) : PeSameVolumeLogError :=
  peSameVolumeLogError_of_parts hK hMT hTU hRHU (scsWardScattering_of_componentPaths hC)
    (scsStageLogMoment_of_passiveLog hPL)

end BlockBand.Endpoints
