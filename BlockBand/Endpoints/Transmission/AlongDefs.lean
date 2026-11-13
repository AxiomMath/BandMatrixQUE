module

public import BlockBand.Transmission.LawDuality.Interface
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Transmission sub-limits along moving energies

This file defines `IsTransmissionSubLimitAlong`, a subsequential limit of the transmission process
along a sequence of energies `e(W)`, and its `W`-free part `IsFiniteLimitProcess`; at a constant
energy the former agrees with `IsTransmissionSubLimit`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform

/-- **`(P, μ)` is a subsequential (fdd) limit along `φ` of the processes at energies `e W`**:
`LawDuality.IsTransmissionSubLimit` with the width-`W` process at energy `e W`. -/
structure IsTransmissionSubLimitAlong (b : ℝ) (e : ℕ → ℝ) (κ : ℝ → ℝ) (φ : ℕ → ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ t, 0 < t → Measurable (μ t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)
  fdd : ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
    ∀ Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Φ (fun i => transmissionProcess b (e (φ n)) κ (φ n) (τ i) ω)
          ∂growthPathLaw (φ n) b) atTop (𝓝 (∫ ω, Φ (fun i => μ (τ i) ω) ∂P))

/-- **The `W`-free part of a limit process**: probability, measurable marginals and a.s.
continuous paths on `(0, ∞)`. -/
structure IsFiniteLimitProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ t, 0 < t → Measurable (μ t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)

/-- At constant energy the along form is `LawDuality.IsTransmissionSubLimit`. -/
theorem isTransmissionSubLimitAlong_const_iff {b E : ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval} :
    IsTransmissionSubLimitAlong b (fun _ => E) κ φ P μ ↔
      BlockBand.Transmission.LawDuality.IsTransmissionSubLimit b E κ φ P μ :=
  ⟨fun h => ⟨h.prob, h.measurable, h.continuous, h.fdd⟩,
    fun h => ⟨h.prob, h.measurable, h.continuous, h.fdd⟩⟩

/-- The `W`-free part of an along sub-limit. -/
theorem IsTransmissionSubLimitAlong.toFinite {b : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimitAlong b e κ φ P μ) : IsFiniteLimitProcess P μ :=
  ⟨h.prob, h.measurable, h.continuous⟩

/-- The `W`-free part of the fixed-energy limit `IsTransmissionLimit`. -/
theorem isFiniteLimitProcess_of_limit {b E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionLimit b E κ P μ) : IsFiniteLimitProcess P μ :=
  ⟨h.prob, h.measurable, h.continuous⟩

end BlockBand.Endpoints.Transmission
