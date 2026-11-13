module

public import BlockBand.Coarea.Native.BlockBand.Counting.EndpointIntensityBoundary
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalUnfoldedIntensity

/-!
# Weak-limit intensity passage and point-state support

This module packages the remaining weak-limit obligations in the
counting argument.  Finite-volume interval intensities are assumed to converge
on closed intervals; this is the precise conclusion which a uniform-
integrability/expectation-passage argument must supply in an application.
Their uniform Lipschitz bounds then pass to the limiting coordinate intensities,
so those intensities are diffuse.  A supplied singleton-expectation identity
turns diffuseness into almost-sure endpoint regularity.

Together with the existing scalar restriction-law convergence and closed
consistency carrier in `BoundaryRegularLimitLawInput`, this proves that the
ambient weak limit is almost surely represented by a projectively consistent,
integer-valued local point state on a translated dense rational family.

The final theorem starts from the concrete tight `PSSSRationalWindowSequence`
and extracts its vague-law subsequence.  Its only remaining argument is
a completion package for each extracted limit: interval expectation passage,
scalar restriction-law convergence, and closed-carrier consistency.  No such
facts are inferred falsely from weak convergence alone.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- Passage data from finite-volume coordinate intensities to the
coordinate intensities of an ambient vague-law limit.

`Icc_tendsto` is the model-facing uniform-integrability (or equivalent
expectation convergence) obligation.  `singleton_expectation` identifies the
resulting finite measure with expected endpoint-fiber mass under the limiting
law. -/
structure CoordinateIntensityPassageInput
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  approximatingIntensity : ℕ → ℕ → FiniteMeasure ℝ
  limitIntensity : ℕ → FiniteMeasure ℝ
  lipschitzConstant : ℕ → ℝ
  lipschitzConstant_nonneg : ∀ n, 0 ≤ lipschitzConstant n
  approximating_Icc_le :
    ∀ i n a b, a < b →
      (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) ≤
        ENNReal.ofReal (lipschitzConstant n * (b - a))
  Icc_tendsto :
    ∀ n a b, a < b →
      Tendsto
        (fun i => (approximatingIntensity i n : Measure ℝ) (Set.Icc a b))
        atTop
        (𝓝 ((limitIntensity n : Measure ℝ) (Set.Icc a b)))
  singleton_expectation :
    ∀ n x,
      ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber x)
        ∂(μ : Measure VagueRationalWindowState) =
      (limitIntensity n : Measure ℝ) {x}

/-- Uniform finite-volume closed-interval bounds pass to every limiting
coordinate intensity through the explicit expectation convergence field. -/
theorem CoordinateIntensityPassageInput.limit_Icc_le
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : CoordinateIntensityPassageInput μ)
    (n : ℕ) {a b : ℝ} (hab : a < b) :
    (input.limitIntensity n : Measure ℝ) (Set.Icc a b) ≤
      ENNReal.ofReal (input.lipschitzConstant n * (b - a)) := by
  exact le_of_tendsto' (input.Icc_tendsto n a b hab) fun i =>
    input.approximating_Icc_le i n a b hab

/-- Every limiting coordinate intensity is diffuse. -/
theorem CoordinateIntensityPassageInput.limit_singleton_eq_zero
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : CoordinateIntensityPassageInput μ) (n : ℕ) (x : ℝ) :
    (input.limitIntensity n : Measure ℝ) {x} = 0 := by
  exact intensity_singleton_eq_zero_of_Icc_lipschitz
    (input.limitIntensity n : Measure ℝ) (input.lipschitzConstant n)
    (input.lipschitzConstant_nonneg n)
    (fun a b hab => input.limit_Icc_le n hab) x

/-- Finite-volume coordinate intensities are diffuse as well. -/
theorem CoordinateIntensityPassageInput.approximating_singleton_eq_zero
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : CoordinateIntensityPassageInput μ) (i n : ℕ) (x : ℝ) :
    (input.approximatingIntensity i n : Measure ℝ) {x} = 0 := by
  exact intensity_singleton_eq_zero_of_Icc_lipschitz
    (input.approximatingIntensity i n : Measure ℝ)
    (input.lipschitzConstant n) (input.lipschitzConstant_nonneg n)
    (fun a b hab => input.approximating_Icc_le i n a b hab) x

/-- Intensity passage supplies endpoint avoidance with no exceptional atoms. -/
def CoordinateIntensityPassageInput.toBoundaryAvoidingEndpointInput
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : CoordinateIntensityPassageInput μ) :
    BoundaryAvoidingEndpointInput μ :=
  boundaryAvoidingEndpointInputOfDiffuseIntensity input.limitIntensity
    input.singleton_expectation input.limit_singleton_eq_zero

/-- A single paper-facing package for completing one ambient vague-law limit.
The first field contains ambient weak convergence, scalar restriction-
law convergence for all translated rational families, and a closed consistency
carrier.  The second field is the intensity expectation passage above. -/
structure WeakLimitPointStateCompletionInput
    [OpensMeasurableSpace VagueRationalWindowState]
    (μs : ℕ → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState) where
  boundaryClosure : BoundaryRegularLimitLawInput atTop μs μ
  intensityPassage : CoordinateIntensityPassageInput μ

/-- A completed ambient limit is almost surely supported on a bundled local
point-state space for a translated dense rational endpoint family. -/
theorem WeakLimitPointStateCompletionInput.exists_shift_ae_lifts_toPointState
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {μs : ℕ → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : WeakLimitPointStateCompletionInput μs μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        ∃ ξ : ShiftedRationalWindowPointState s, ξ.1 = ν) :=
  input.boundaryClosure.exists_shift_ae_lifts_toPointState
    input.intensityPassage.toBoundaryAvoidingEndpointInput

/-- The expanded almost-sure conclusion, retaining consistency and all
natural-valued determining-family masses. -/
theorem WeakLimitPointStateCompletionInput.exists_shift_ae_consistent_integer
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {μs : ℕ → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    (input : WeakLimitPointStateCompletionInput μs μ) :
    ∃ s : ℝ,
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        IsConsistentLocalWindowEncoding ν ∧
        HasNaturalLocalRestrictionMass
          (shiftedRationalDeterminingFamily s) ν) :=
  input.boundaryClosure.exists_shift_ae_consistent_integer
    input.intensityPassage.toBoundaryAvoidingEndpointInput

/-- **Concrete common-state subsequence theorem.**  PSSS local first moments
produce a weakly convergent subsequence in the ambient product
of finite-measure spaces.  If every extracted limit is supplied with the exact
completion data isolated above, then one extracted limit is almost surely a
consistent integer local point state on a dense translated rational family.

The completion function is deliberately explicit: weak convergence alone does
not imply convergence of unbounded count expectations, sharp scalar restriction
laws, or closure of projective consistency. -/
theorem PSSSRationalWindowSequence.exists_vague_limit_ae_pointState
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    [HasOuterApproxClosed VagueRationalWindowState]
    {input : PSSSInput.{0}} (seq : PSSSRationalWindowSequence input)
    (complete : ∀ (μ : ProbabilityMeasure VagueRationalWindowState)
      (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) →
      WeakLimitPointStateCompletionInput (seq.vagueLaw ∘ φ) μ) :
    ∃ (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ) (s : ℝ),
      StrictMono φ ∧
      Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) ∧
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        ∃ ξ : ShiftedRationalWindowPointState s, ξ.1 = ν) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := seq.exists_vague_weak_subsequence
  obtain ⟨s, hdense, hcount, hae⟩ :=
    (complete μ φ hφ hlim).exists_shift_ae_lifts_toPointState
  exact ⟨μ, φ, s, hφ, hlim, hdense, hcount, hae⟩

end CoareaNative.BlockBand
