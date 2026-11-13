module

public import BlockBand.Asymptotics.CriticalSequence
public import BlockBand.Model.Observables
public import BlockBand.PointProcess.LawProperties
public import BlockBand.PointProcess.Specifications

/-!
# Mathematical vocabulary for the three main statements

The definitions here contain no paper-specific analytic certificate. They fix
only the exact finite model, observables, topologies, and characterizations
needed to state the main theorems of the paper.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open Filter MeasureTheory Topology
open scoped ContDiff

/-- Positive critical ratios. -/
abbrev PositiveRatio := {τ : ℝ // 0 < τ}

/-- An exact finite realization of the physical Gaussian model and ordered
spectral observables. -/
structure FiniteRealization (p : Parameters) where
  model : p.GaussianRingModel
  spectral : p.SpectralRealization model

/-- Law of the physical unfolded marked point process. -/
def FiniteRealization.markedLaw {p : Parameters}
    (R : FiniteRealization p) (E : ℝ) : ProbabilityMeasure MarkedPointMeasure :=
  R.model.law.map (R.spectral.markedConfig E)

/-- One-based bulk-rank convention of the QUE theorem. -/
def IsBulkRank (p : Parameters) (θ : ℝ) (α : Fin p.N) : Prop :=
  θ ≤ ((α.val + 1 : ℕ) : ℝ) / p.N ∧
    ((α.val + 1 : ℕ) : ℝ) / p.N ≤ 1 - θ

/-- The exact characterization of the all-ratio critical family in the critical
theorem. Convergence is required for every sequence with `W → ∞` and
`n/W → τ`, with no rate, parity, or monotonicity condition. -/
def IsCriticalFamily (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure) : Prop :=
  Measurable MarkedPointMeasure.spectralProjection ∧
  (∀ τ : PositiveRatio, ∀ s : CriticalSequence τ.1,
    Nonempty (∀ j, FiniteRealization (s.parameters b hb hb' j))) ∧
  (∀ τ : PositiveRatio, ∀ s : CriticalSequence τ.1,
    ∀ R : ∀ j, FiniteRealization (s.parameters b hb hb' j),
      Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 (family τ))) ∧
  (∀ τ, HasSimpleSpectralLocations (family τ)) ∧
  (∀ τ, HasUnitSpectralIntensity (family τ)) ∧
  (∀ τ, HasUniformSpatialIntensity (family τ)) ∧
  (∀ τ, IsSpectrallyStationary (family τ)) ∧
  (∀ τ, IsMarkRotationInvariant (family τ))

/-- Smooth nonnegative unit-mass spectral weight. -/
structure SpectralWeight where
  toContinuousMap : ContinuousMap ℝ ℝ
  smooth : ContDiff ℝ ∞ toContinuousMap
  compactSupport : HasCompactSupport toContinuousMap
  nonnegative : ∀ x, 0 ≤ toContinuousMap x
  integral_eq_one : ∫ x, toContinuousMap x = 1

instance : CoeFun SpectralWeight (fun _ => ℝ → ℝ) :=
  ⟨fun w => w.toContinuousMap⟩

/-- Smooth real nonconstant test of a mass profile on the unit torus. -/
structure ProfileTest where
  toContinuousMap : ContinuousMap Torus ℝ
  smooth_lift : ContDiff ℝ ∞ (fun x : ℝ => toContinuousMap (QuotientAddGroup.mk x))
  nonconstant : ∃ x y, toContinuousMap x ≠ toContinuousMap y

instance : CoeFun ProfileTest (fun _ => Torus → ℝ) :=
  ⟨fun φ => φ.toContinuousMap⟩

/-- Finite physical profile variance, with the physical unfolding and no
expectation/supremum interchange. -/
def FiniteRealization.profileVariance {p : Parameters}
    (R : FiniteRealization p) (E : ℝ)
    (w : SpectralWeight) (φ : ProfileTest) : ℝ :=
  ∫ H,
    ∑ α : Fin p.N,
      w (R.spectral.unfoldedEigenvalue E H α) *
        |(∫ r, φ r ∂(R.spectral.profile H α : Measure Torus)) -
          ∫ r, φ r| ^ 2
    ∂(R.model.law : Measure p.SiteMatrix)

/-- The complete endpoint assertion for a fixed already-characterized critical
family. Endpoint limits occur only after the fixed-ratio critical limit. -/
def HasCriticalEndpoints (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure) : Prop :=
  ∃ variance : PositiveRatio → ProfileTest → ℝ,
    (∀ τ : PositiveRatio, ∀ w : SpectralWeight, ∀ φ : ProfileTest,
      ∀ s : CriticalSequence τ.1,
      ∀ R : ∀ j, FiniteRealization (s.parameters b hb hb' j),
        Tendsto (fun j => (R j).profileVariance E w φ)
          atTop (𝓝 (variance τ φ))) ∧
    (∀ τ φ, 0 < variance τ φ) ∧
    (∀ φ, Tendsto (fun τ : PositiveRatio => variance τ φ) atBot (𝓝 0)) ∧
    (∃! sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ),
      IsSineLaw sineLaw) ∧
    (∀ sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ),
      IsSineLaw sineLaw →
      Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ))
        atBot (𝓝 sineLaw)) ∧
    (∃! poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ),
      IsUnitPoissonLaw poissonLaw) ∧
    (∀ poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ),
      IsUnitPoissonLaw poissonLaw →
      Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ))
        atTop (𝓝 poissonLaw))

end BlockBand
