module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface

/-!
# `ComplexSourceConstruction`: the decomposition into named steps

* `ComplexModelExists`: the complex finite model exists for every entrance carried by transmission
  sequences.
* `ComplexCapRemoval`: the model values converge as the count cap `K → ∞`.
* `ComplexCutoffRemoval`: then as the current cutoff `h ↓ 0` (extended rank-free coupling).
* `ComplexPhysicalApproximation`: the finite-width expectations are eventually close to the model
  values.
* `ComplexSourceTight`: the finite-width laws of the source data are tight.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal

/-- The expectation `E Φ(𝒦, M_pr, B_pr, J_pr)` at width `W` and final length `⌊WT⌋` (the
integrand of `IsComplexSourceLimit`). -/
def physExpectation (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (W : ℕ) : ℝ :=
  ∫ x, Φ (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x) ∂probedPathLaw W np b

/-- The law of the source data at width `W` and final length `⌊WT⌋`. -/
def physLaw (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) : Measure (SourceData np) :=
  (probedPathLaw W np b).map (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m)

/-- **Ambient existence of the complex finite model**: the initial frame and the existence part of
the finite Gram law proposition, births perpendicular in unused near dimensions, near probe births
and retained modes, the added equation `d𝒦 = -2iηV_pr*dAV_pr` and the births `a m_j`. On the
domain, for a source-free start `0 < s < min τ_j`, every law `ρ` of a random transmission
sequence, cutoff `h > 0` and cap `K`, a complex finite model with entrance `ρ.map seqTraceMeasure`
exists. -/
def ComplexModelExists : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) →
  ∀ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ → (∀ᵐ t ∂ρ, IsTransmissionSequence t) →
  ∀ (h : ℝ) (K : ℕ), 0 < h →
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
      (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
      (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
      IsFiniteComplexSourceModel b E s τ m h K (ρ.map seqTraceMeasure) 𝓖 Q tseq G Kc

/-- **Removal of the count cap**, as in the source process theorem (by the homogeneous fractional
trace bound): for a homogeneous transmission limit, at a fixed cutoff `h > 0`, complex model values
at every cap converge as `K → ∞`. -/
def ComplexCapRemoval : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ h : ℝ, 0 < h → ∀ Ψ : ℕ → ℝ,
    (∀ K, ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ (Ψ K)) →
    ∃ Λ : ℝ, Tendsto Ψ atTop (𝓝 Λ)

/-- **Removal of the current cutoff**: the rank-free coupling extends to the complex source
equation, and Burkholder and the frame coupling make the complex source paths Cauchy as the current
cutoff is removed. If `Ψ K h` are complex model values and `Ψ(·,h) → Λ(h)`, then `Λ` converges
along `𝓝[>] 0`. -/
def ComplexCutoffRemoval : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ (Ψ : ℕ → ℝ → ℝ) (Λ : ℝ → ℝ),
    (∀ K h, 0 < h → ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ (Ψ K h)) →
    (∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h))) →
    ∃ Λ' : ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 Λ')

/-- **Identification at finite retained rank and the closing error**: the complex source update,
the mean and centred sizes of the `𝒦` multiplier in the mixed-word argument, the brackets and the
births; at finite retained current rank the surviving noise is the complex source SDE, and the real
part of the closing error is paid after phase averaging through the conjugate Kolmogorov equation.
For every `ε > 0` there is `h₀ > 0` such that for every `h ∈ (0, h₀)` there is `K₀` such that for
every cap `K ≥ K₀` and every complex model value `v` at `(h, K)`, eventually in `W`, the
width-`W` expectation of `Φ` is within `ε` of `v`. -/
def ComplexPhysicalApproximation : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ v : ℝ,
      ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ v →
      ∀ᶠ W in atTop, |physExpectation b E T τ m Φ W - v| ≤ ε

/-- **Tightness of the finite-width laws** (all fixed source moments, including the fixed `𝒦` moments,
are bounded): on the domain, the laws of the source data at final length `⌊WT⌋`, `W ∈ ℕ`, form a
tight set. -/
def ComplexSourceTight : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
    IsTightMeasureSet (Set.range fun W : ℕ => physLaw b E T τ m W)

end BlockBand.SourceProcess.ComplexConstruct
