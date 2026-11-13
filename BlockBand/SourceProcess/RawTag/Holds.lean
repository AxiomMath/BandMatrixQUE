module

public import BlockBand.SourceProcess.RawTag.Main
public import BlockBand.SourceProcess.RawTag.UpdPins
public import BlockBand.SourceProcess.ComplexSourceLaw.Extended

/-!
# `RawTagMoments` from the contract hypotheses

* `rawTagMoments_holds`: under `GaussianAbsorptionContract`, `GaussianLpGradient`,
  `ScalarRecursionContract` and `MatchedTracesContract`, the raw tag moments `RawTagMoments` hold.
* corollaries: the field `moments` (`moments_holds`), the field `extendedSourceMoments`
  (`extendedSourceMoments_holds`), and `ComplexSourceLawContract` from the two further
  hypotheses `ComplexFiniteUniqueness`, `ComplexSourceConstruction`
  (`complexSourceLawContract_of_baseContracts`; `ComplexFiniteUniqueness` is proved as
  `ComplexSplit.complexFiniteUniqueness_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw

/-- `RawTagMoments` from the input hypotheses. -/
theorem rawTagMoments_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : RawTagMoments :=
  rawTagMoments_of rawUpdate_holds rawBirth_holds hGA hLp hSR hMT

/-- The field `ComplexSourceLawContract.moments` from the input hypotheses. -/
theorem moments_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ p : ℝ, 1 ≤ p → ∀ T₀ : ℝ, ∃ C : ℝ, ∀ T : ℝ, (∀ j, τ j < T) → T ≤ T₀ →
      ∀ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν →
        ∫⁻ y, ENNReal.ofReal (sourceDataMoment p y) ∂ν ≤ ENNReal.ofReal C :=
  moments_of_raw (rawTagMoments_holds hGA hLp hSR hMT)

/-- The field `ComplexSourceLawContract.extendedSourceMoments` from the input hypotheses. -/
theorem extendedSourceMoments_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) :
    ExtendedSourceMoments :=
  extendedSourceMoments_of_raw (rawTagMoments_holds hGA hLp hSR hMT)

/-- The `ComplexSourceLawContract` from the two further hypotheses `ComplexFiniteUniqueness`,
`ComplexSourceConstruction` and the input hypotheses. -/
theorem complexSourceLawContract_of_baseContracts (hU : ComplexFiniteUniqueness)
    (hC : ComplexSourceConstruction) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : ComplexSourceLawContract :=
  complexSourceLawContract_of' hU hC (rawTagMoments_holds hGA hLp hSR hMT)

end BlockBand.SourceProcess.RawTag
