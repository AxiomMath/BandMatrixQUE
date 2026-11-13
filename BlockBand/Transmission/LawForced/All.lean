module

public import BlockBand.Transmission.LawForced.LimitMart
public import BlockBand.Transmission.LawForced.MassBound
public import BlockBand.Transmission.LawForced.ForcingRate
public import BlockBand.Transmission.LawDuality.SubLimitExists
public import BlockBand.Transmission.Absorbed.OneTime
public import BlockBand.Transmission.LawFinite.LawFiniteAll

/-!
# The `law` field of the transmission law from the forced expansion

`law_of_forced`: under the input hypotheses and the transmission generator theorem, the `law`
field follows from the hypotheses (statements defined elsewhere)
`AbsorbedPowerModulus` (part of `AbsorbedPowerTight`), `RatioDriftSummable` (which gives
`SubLimitRatioMartingale` by `subLimitRatioMartingale_of`), `RatioDualityPrinciple` and
`SubLimitFddUnique`. The mass bound is `subLimitMassBound_holds hMT hGA hLp` and the entrance is
`transmissionEntranceBulk_of_baseContracts hMT hGA hLp`; the existence of subsequential limits
and the trace modulus come from `law_of_tight`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Absorbed

/-- **The `law` field of the transmission law** from the input hypotheses, `hTG` and
`AbsorbedPowerModulus`, `RatioDriftSummable`, `RatioDualityPrinciple`, `SubLimitFddUnique`. -/
theorem law_of_forced (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hTG : TransmissionGeneratorContract)
    (hMod : AbsorbedPowerModulus) (hRD : RatioDriftSummable) (hPr : RatioDualityPrinciple)
    (hUniq : SubLimitFddUnique) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) :=
  law_of_tight hTG (absorbedPowerTight_of_modulus hMT hGA hLp hMod)
    (subLimitRatioMartingale_of hRD) (subLimitMassBound_holds hMT hGA hLp)
    (LawFinite.transmissionEntranceBulk_of_baseContracts hMT hGA hLp) hPr hUniq

end BlockBand.Transmission.LawForced
