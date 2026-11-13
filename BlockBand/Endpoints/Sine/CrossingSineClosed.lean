module

public import BlockBand.Endpoints.Sine.GUELawBridge

/-!
# The crossing sine lemma with the GUE law bridge supplied

`crossingSine_of_contracts` is `crossingSine` with the hypothesis `GUELawBridge` supplied by
`guelawBridge_holds`: the crossing Laplace functionals converge to the sine Laplace functional
under `ExternalSine`, `CoareaContract` and `PairRegularEventContract`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal

/-- **The crossing process has a sine limit**, from `ExternalSine`, `CoareaContract` and
`PairRegularEventContract` only. For every ratio
`τ`, critical sequence, `0 < b < 1/2`, bulk `E`, physical models and pair choices, and every
nonnegative `f ∈ C_c(ℝ)`, the Laplace transform of the crossing configuration converges to
the intensity-one sine Laplace functional.
-/
theorem crossingSine_of_contracts (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) :
    ∀ (τ : ℝ) (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E → E < 2 →
      ∀ (model : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
        (i : ∀ j, ZMod (s.parameters b hb hb' j).n)
        (f : CompactlySupportedContinuousMap ℝ ℝ), (∀ x, 0 ≤ f x) →
          Tendsto (fun j => crossingLaplace (s.parameters b hb hb' j) (model j) (i j) E f) atTop
            (𝓝 (ENNReal.ofReal (sineLaplaceFunctional f))) :=
  crossingSine hExt hCo hPair guelawBridge_holds

end BlockBand.Endpoints
