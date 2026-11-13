module

public import BlockBand.Window.SmallCriticalHolds

/-!
# The window transfer and small-ratio critical theorems from the PSSS source theorem alone

Versions of the window transfer theorem and of the small-ratio critical theorem with the
hypothesis `inputs : NativeInputs.{0}` replaced by `hpsss : PSSS.SourceContract.{0}`. The
original chain `Window.windowTransfer_holds` → `Count.sharperFreshCount_holds` →
`Count.sharperFreshCount_of_obligations` uses `inputs` only through
`gueWindowFactorialBound_of inputs.psss hLaw`, and `Window.smallCritical_of_layerContracts` uses `inputs`
only through `windowTransfer_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.ReducedInputs

open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Inputs
open BlockBand.Window BlockBand.Window.Count

/-- `Window.Count.sharperFreshCount_of_obligations` with `inputs` replaced by its `psss` field. -/
theorem sharperFreshCount_of_obligations_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hLp : GaussianLpGradient) (hLaw : GueNativeLaw) (hD : SpectralCoordinateGradient) :
    SharperFreshCountStatement :=
  sharperFreshCount_of_gueBounds (gueWindowFactorialBound_of hpsss hLaw) (gueSpectralLpGradient_of hLp hD)

/-- `Window.Count.sharperFreshCount_holds` with `inputs` replaced by its `psss` field. -/
theorem sharperFreshCount_holds_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hLp : GaussianLpGradient) : SharperFreshCountStatement :=
  sharperFreshCount_of_obligations_psss hpsss hLp gueNativeLaw_holds spectralCoordinateGradient_holds

/-- **`Window.windowTransfer_holds`, from PSSS only**: `WindowAngular.WindowTransferContract`. -/
theorem windowTransfer_holds_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hLp : Inputs.GaussianLpGradient) (hMT : Layers.MatchedTracesContract)
    (hRing : Layers.RingCompensatedPhaseContract) (hRank : Layers.RankLocationContract)
    (hFresh : Layers.FreshCountContract) : WindowAngular.WindowTransferContract :=
  Transfer.windowTransfer_of_refinedCount
    (Count.refinedCount_holds (sharperFreshCount_holds_psss hpsss hLp) hMT hRing hRank hFresh)

/-- **`Window.smallCritical_of_layerContracts`, from PSSS only**: `WindowAngular.SmallCriticalContract`. -/
theorem smallCritical_of_layerContracts_psss (hpsss : BlockBand.External.PSSS.SourceContract.{0})
    (hLp : Inputs.GaussianLpGradient) (hMT : Layers.MatchedTracesContract)
    (hRing : Layers.RingCompensatedPhaseContract) (hRank : Layers.RankLocationContract)
    (hFresh : Layers.FreshCountContract) (w : QUE.PairCenterFamily)
    (hc : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      QUE.PhysicalCenterContract b θ T hb hb' w)
    (ha : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      QUE.PhysicalAngularModeContract b θ T hb hb' w) :
    WindowAngular.SmallCriticalContract :=
  SmallCritical.smallCritical_holds (windowTransfer_holds_psss hpsss hLp hMT hRing hRank hFresh)
    (fun b θ T hb hb' h0 h1 => BlockBand.QUE.ModeBoundOfContracts.modeBound_of_contracts b θ T hb hb'
      w (hc b θ T hb hb' h0 h1) (ha b θ T hb hb' h0 h1))

end BlockBand.Internal.ReducedInputs
