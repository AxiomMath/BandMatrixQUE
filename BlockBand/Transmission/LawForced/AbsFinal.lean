module

public import BlockBand.Transmission.LawForced.Final
public import BlockBand.Transmission.LawForced.AbsSum

/-!
# The `law` field from the absorbed moment bounds

`law_of_absorbed_pins`: under the input hypotheses, `AbsorbedJetMoments` and
`AbsorbedSourceMixingBulk`, every admissible profile has a transmission limit satisfying the
dual law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Transmission.LawDuality
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws

/-- **The `law` field of the transmission law** from the input hypotheses and the two absorbed
moment bounds `Absorbed.AbsorbedJetMoments` (proved as `Absorbed.absorbedJetMoments_holds`) and
`Absorbed.AbsorbedSourceMixingBulk` (proved as `Absorbed.absorbedSourceMixingBulk_holds`). -/
theorem law_of_absorbed_pins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hJ : BlockBand.Transmission.Absorbed.AbsorbedJetMoments)
    (hMix : BlockBand.Transmission.Absorbed.AbsorbedSourceMixingBulk) :
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
  law_of_ratioDriftSummable hMT hGA hLp hP (ratioDriftSummable_of_pins hMT hGA hLp hP hJ hMix)

end BlockBand.Transmission.LawForced
