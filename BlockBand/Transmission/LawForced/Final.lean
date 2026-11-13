module

public import BlockBand.Transmission.LawDuality.FddMulti
public import BlockBand.Transmission.LawDuality.All
public import BlockBand.Transmission.LawDuality.SubLimitAll
public import BlockBand.Transmission.LawForced.All
public import BlockBand.Transmission.Absorbed.ModulusAlong
public import BlockBand.Transmission.Generator.ProdMain

/-!
# The `law` field from `RatioDriftSummable`

`law_of_ratioDriftSummable`: under the input hypotheses, `RatioDriftSummable` gives the `law`
field of the transmission law; the other inputs of `law_of_forced` are proved theorems.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Transmission.LawDuality
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws

/-- **The `law` field from the input hypotheses and `RatioDriftSummable`.** -/
theorem law_of_ratioDriftSummable (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hRD : RatioDriftSummable) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, BlockBand.Internal.Contracts.TransmissionPath.IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
        (μ : ℝ → Ω → MeasureTheory.FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ),
          BlockBand.Internal.Contracts.TransmissionPath.IsRatioParameter x y →
          HasDualDeletionProcess (BlockBand.Internal.Contracts.TransmissionPath.transportD0 b E)
            x y ∧
          DualLawValue E κ t (BlockBand.Internal.Contracts.TransmissionPath.transportD0 b E) x y
            (∫ ω, BlockBand.Internal.Contracts.TransmissionPath.transmissionRatio x y (μ t ω)
              ∂P) :=
  have hTG := BlockBand.Transmission.Generator.transmissionGenerator_holds hMT hGA hLp hP
  have hMP : SubLimitRatioMP := subLimitRatioMP_of (subLimitRatioMartingale_of hRD)
    (subLimitMassBound_holds hMT hGA hLp)
    (BlockBand.Transmission.LawFinite.transmissionEntranceBulk_of_baseContracts hMT hGA hLp)
  law_of_forced hMT hGA hLp hTG
    (BlockBand.Transmission.Absorbed.absorbedPowerModulus_holds hMT hGA hLp) hRD
    ratioDualityPrinciple_holds (subLimitFddUnique_of_ratioMP hMP)

end BlockBand.Transmission.LawForced
