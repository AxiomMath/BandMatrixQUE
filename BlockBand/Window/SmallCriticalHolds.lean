module

public import BlockBand.Window.SmallCritical.Assembly
public import BlockBand.Window.WindowTransferHolds
public import BlockBand.QUE.Assembly.ModeBoundOfContracts

/-!
# The small-ratio critical theorem

`smallCritical_of_layerContracts` proves `WindowAngular.SmallCriticalContract` (variance and mode bounds
and diffuseness of the profile marks of critical marked limits) from the Peled–Schenker–Shamis–Sodin
(PSSS) inputs, the layer inputs and the physical centre and angular-mode inputs, via the window
transfer theorem. Hypotheses: `NativeInputs`, `GaussianLpGradient`, `MatchedTracesContract`,
`RingCompensatedPhaseContract`, `RankLocationContract`, `FreshCountContract`, and, for one centre
family `w` at every `(b, ϑ, T)`, `PhysicalCenterContract` and `PhysicalAngularModeContract`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Window

open BlockBand.Internal.Contracts

/-- **The small-ratio critical theorem** `WindowAngular.SmallCriticalContract`, from the PSSS
inputs, `GaussianLpGradient`, the layer contracts and the physical centre and angular-mode
contracts.
-/
theorem smallCritical_of_layerContracts (inputs : BlockBand.External.NativeInputs.{0})
    (hLp : Inputs.GaussianLpGradient) (hMT : Layers.MatchedTracesContract)
    (hRing : Layers.RingCompensatedPhaseContract) (hRank : Layers.RankLocationContract)
    (hFresh : Layers.FreshCountContract) (w : QUE.PairCenterFamily)
    (hc : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      QUE.PhysicalCenterContract b θ T hb hb' w)
    (ha : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      QUE.PhysicalAngularModeContract b θ T hb hb' w) :
    WindowAngular.SmallCriticalContract :=
  SmallCritical.smallCritical_holds (windowTransfer_holds inputs hLp hMT hRing hRank hFresh)
    (fun b θ T hb hb' h0 h1 => BlockBand.QUE.ModeBoundOfContracts.modeBound_of_contracts b θ T hb hb'
      w (hc b θ T hb hb' h0 h1) (ha b θ T hb hb' h0 h1))

end BlockBand.Window
