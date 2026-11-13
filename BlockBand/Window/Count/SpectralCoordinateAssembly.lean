module

public import BlockBand.Window.Count.SharperFreshCountAssembly
public import BlockBand.Window.Count.GueNativeLawHolds
public import BlockBand.Window.Count.SpectralCoordinateGradientHolds

/-!
# The sharper fresh count from the external inputs

`sharperFreshCount_holds` proves `SharperFreshCountStatement` from the Peled–Schenker–Shamis–Sodin
(PSSS) input and the Gaussian
`L^p` gradient bound alone, by discharging the two other hypotheses of
`sharperFreshCount_of_obligations`:

* `gueNativeLaw_holds : GueNativeLaw` (a Gaussian law identification);
* `spectralCoordinateGradient_holds : SpectralCoordinateGradient` (the deterministic
  trace-derivative identity).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open BlockBand.Internal.Contracts.Inputs

/-- **`SharperFreshCountStatement`**, from the PSSS source contract `inputs.psss` and the input
hypothesis `hLp : GaussianLpGradient` only.
Law
`gueMeasure (Fin W) (c/W)`;
`∀ c > 0, ∀ p ≥ 1, ∃ C`, uniformly in `W ≥ 1`, Hermitian `F`
and `e ∈ ℝ`:
`‖N_-(A+F-e) - E N_-(A+F-e)‖_p ≤ C W^{1/3}`.
-/
theorem sharperFreshCount_holds (inputs : BlockBand.External.NativeInputs.{0})
    (hLp : GaussianLpGradient) : SharperFreshCountStatement :=
  sharperFreshCount_of_obligations inputs hLp gueNativeLaw_holds spectralCoordinateGradient_holds

end BlockBand.Window.Count
