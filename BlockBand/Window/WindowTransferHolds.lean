module

public import BlockBand.Window.Transfer.WindowTransfer
public import BlockBand.Window.Count.RefinedCountLocation
public import BlockBand.Window.Count.SpectralCoordinateAssembly

/-!
# The window transfer theorem

`windowTransfer_holds` proves `WindowAngular.WindowTransferContract` from the Peled–Schenker–Shamis–Sodin
(PSSS) inputs and the
layer inputs, via the refined count `refinedCount_holds` and the sharper fresh count
`sharperFreshCount_holds`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Window

open BlockBand.Internal.Contracts

/-- **The window transfer theorem** `WindowAngular.WindowTransferContract`, from `NativeInputs`,
`GaussianLpGradient`, `MatchedTracesContract`, `RingCompensatedPhaseContract`,
`RankLocationContract` and `FreshCountContract`.
-/
theorem windowTransfer_holds (inputs : BlockBand.External.NativeInputs.{0})
    (hLp : Inputs.GaussianLpGradient) (hMT : Layers.MatchedTracesContract)
    (hRing : Layers.RingCompensatedPhaseContract) (hRank : Layers.RankLocationContract)
    (hFresh : Layers.FreshCountContract) : WindowAngular.WindowTransferContract :=
  Transfer.windowTransfer_of_refinedCount
    (Count.refinedCount_holds (Count.sharperFreshCount_holds inputs hLp) hMT hRing hRank hFresh)

end BlockBand.Window
