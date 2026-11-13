module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The complex source limit along every sequence of path lengths

The statement that a critical limit `ν` of the complex source data at final time `T` is also the
limit along every sequence of widths `W_j → ∞` and path lengths `r_j` with `r_j/W_j → T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionSequences
open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

/-- The joint law of the source data at width `Wseq j` and path length `rseq j` converges to `ν`
against every bounded continuous test. -/
def IsComplexSourceLimitAlong (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (ν : Measure (SourceData np))
    (Wseq rseq : ℕ → ℕ) : Prop :=
  ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
    Tendsto (fun j : ℕ => ∫ x, Φ (complexSourceData b E (Wseq j) (rseq j) τ m x)
      ∂probedPathLaw (Wseq j) np b) atTop (𝓝 (∫ y, Φ y ∂ν))

/-- On the domain of
`ComplexSourceLawContract.limit`: whenever `ν` is the complex source limit at final time `T`
(`IsComplexSourceLimit`, i.e. along `⌊W T⌋₊`), the source data converge to the same `ν`
along every sequence of widths `W_j → ∞` and path lengths `r_j` with `r_j / W_j → T`.
-/
structure ComplexSourceLimitSequenceContract : Prop where
  everySequence : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ T : ℝ, (∀ j, τ j < T) →
    ∀ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν →
    ∀ Wseq rseq : ℕ → ℕ, Tendsto Wseq atTop atTop →
      Tendsto (fun j => (rseq j : ℝ) / (Wseq j : ℝ)) atTop (𝓝 T) →
        IsComplexSourceLimitAlong b E τ m ν Wseq rseq

example (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (ν : Measure (SourceData np)) :
    IsComplexSourceLimit b E T τ m ν ↔
      IsProbabilityMeasure ν ∧ IsComplexSourceLimitAlong b E τ m ν id (fun W => ⌊(W : ℝ) * T⌋₊) :=
  Iff.rfl

end BlockBand.Internal.Contracts.TransmissionSequences
