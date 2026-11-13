module

public import BlockBand.Window.Count.GueWindowFactorial
public import BlockBand.Window.Count.SpectralGradientTransfer

/-!
# The sharper fresh count: assembly

`sharperFreshCount_of_obligations` proves `SharperFreshCountStatement` from the Peled–Schenker–Shamis–Sodin
(PSSS) input, the Gaussian `L^p` gradient bound, the one-block law identification `GueNativeLaw` and the trace
gradient identity `SpectralCoordinateGradient`. The form with these two identities discharged, from
the PSSS input and the gradient bound only, is `sharperFreshCount_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open BlockBand.Internal.Contracts.Inputs

/-- **`SharperFreshCountStatement`, conditional assembly.** Law `gueMeasure (Fin W) (c/W)`;
`∀ c > 0, ∀ p ≥ 1, ∃ C`, then every `W ≥ 1`, Hermitian `F` (no norm bound) and real `e`:
`‖N_-(A+F-e) - E N_-(A+F-e)‖_p ≤ C W^{1/3}`.
Dependencies: `inputs.psss` (the PSSS source contract), `hLp : GaussianLpGradient` (an input
hypothesis), and the hypotheses `hLaw : GueNativeLaw` and `hD : SpectralCoordinateGradient`
(proved as `gueNativeLaw_holds` and `spectralCoordinateGradient_holds`).
-/
theorem sharperFreshCount_of_obligations (inputs : BlockBand.External.NativeInputs.{0})
    (hLp : GaussianLpGradient) (hLaw : GueNativeLaw) (hD : SpectralCoordinateGradient) :
    SharperFreshCountStatement :=
  sharperFreshCount_of_gueBounds (gueWindowFactorialBound_of inputs.psss hLaw)
    (gueSpectralLpGradient_of hLp hD)

end BlockBand.Window.Count
