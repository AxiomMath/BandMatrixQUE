module

public import BlockBand.Transmission.LawForced.AbsFinal
public import BlockBand.Transmission.Absorbed.MixBulk
public import BlockBand.Transmission.LawClauses.JetGap
public import BlockBand.Transmission.LawClauses.FractionalHessian
public import BlockBand.Transmission.LawClauses.EntryVarianceHolds
public import BlockBand.Transmission.LawDuality.Determining
public import BlockBand.Transmission.LawFractional.Main
public import BlockBand.Transmission.LawFractional.NoMass
public import BlockBand.Transmission.LawDecay.ExpDecay

/-!
# The transmission law from the input hypotheses

`TransmissionLawContract` holds under `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient` and `GaussianPoincare`.

* **`transmissionLawContract_holds hMT hGA hLp hP : TransmissionLawContract`**: every field from
  its proved theorem: `law` (`law_holds`), `fractional` (`LawFractional.fractional_holds`),
  `noMassAtZero` (`LawFractional.noMassAtZero_holds`), `expDecay` (`LawDecay.expDecay_holds`),
  `determining` (`LawDuality.determining_holds`), `fractionalHessian`
  (`LawClauses.fractionalHessian`), `jetGap` (`LawClauses.jetGap`), `entryVariance`
  (`LawClauses.entryVariance_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Transmission.LawDuality
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws

/-- **The `law` field from the input hypotheses.** -/
theorem law_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
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
  law_of_absorbed_pins hMT hGA hLp hP
    (BlockBand.Transmission.Absorbed.absorbedJetMoments_holds hMT hGA hLp)
    (BlockBand.Transmission.Absorbed.absorbedSourceMixingBulk_holds hMT hGA hLp)

/-- **The `TransmissionLawContract` from the input hypotheses.** -/
theorem transmissionLawContract_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    TransmissionLawContract where
  law := law_holds hMT hGA hLp hP
  fractional := LawFractional.fractional_holds hMT hGA hLp hP
  noMassAtZero := LawFractional.noMassAtZero_holds hMT hGA hLp hP
  expDecay := LawDecay.expDecay_holds hMT hGA hLp hP
  determining := determining_holds
  fractionalHessian := LawClauses.fractionalHessian
  jetGap := LawClauses.jetGap
  entryVariance := LawClauses.entryVariance_holds hGA hLp hP

end BlockBand.Transmission.LawForced
