module

public import BlockBand.Coarea.Native.BlockBand.Probability.NaturalRestrictionCountLaw
public import BlockBand.Coarea.Native.BlockBand.Counting.SmoothedClosePairTopology

/-!
# Concrete weak-limit input for the paper counting theorem

This module assembles the limit package after the analytic estimates have been
proved.  Ambient vague convergence now implies every scalar restriction-law
convergence by the a.e.-continuous mapping theorem; uniform exponential
moments then imply count uniform integrability.  Smoothed bump events supply
the open close-pair sets and detect multiplicity collisions.

The remaining fields are model data: intensity identifications and
bounds, boundary-nullness, finite-volume exponential/close-pair estimates,
and closed validity of the mark constraint.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

universe u

/-- Model-specific quantitative data remaining after all generic weak-limit,
uniform-integrability, and close-pair topology arguments have been discharged. -/
structure ConcretePaperCountingLimitInput
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState]
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ) where
  ambient_tendsto : Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ)
  consistency : ConsistentLimitLawClosureInput atTop (seq.vagueLaw ∘ φ) μ
  rational_boundary_null : ∀ s n q,
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      (ν n : Measure (MarkedSpectralSpace Unit))
        (frontier (shiftedRationalDeterminingFamily s n q)) = 0
  rational_approximants_natural : ∀ s i,
    ∀ᵐ ν ∂((seq.vagueLaw ∘ φ) i : Measure VagueRationalWindowState),
      HasNaturalLocalRestrictionMass (shiftedRationalDeterminingFamily s) ν

  /-- The real-endpoint restriction family used to identify intensities. -/
  countSets : ℕ → (ℝ × ℝ) → Set (MarkedSpectralSpace Unit)
  countSets_measurable : ∀ n q, MeasurableSet (countSets n q)
  countSets_boundary_null : ∀ n q,
    ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      (ν n : Measure (MarkedSpectralSpace Unit))
        (frontier (countSets n q)) = 0
  countSets_approximants_natural : ∀ i,
    ∀ᵐ ν ∂((seq.vagueLaw ∘ φ) i : Measure VagueRationalWindowState),
      HasNaturalLocalRestrictionMass countSets ν
  countExponent : ℕ → ℝ → ℝ → ℝ
  countBound : ℕ → ℝ → ℝ → ℝ
  countExponent_pos : ∀ n a b, a < b → 0 < countExponent n a b
  countBound_nonneg : ∀ n a b, a < b → 0 ≤ countBound n a b
  countExp_integrable : ∀ i n a b, a < b → Integrable
    (fun x : NNReal => Real.exp (countExponent n a b * (x : ℝ)))
    (localRestrictionMassLaw ((seq.vagueLaw ∘ φ) i)
      countSets n (a, b) : Measure NNReal)
  countExp_le : ∀ i n a b, a < b →
    ∫ x : NNReal, Real.exp (countExponent n a b * (x : ℝ))
        ∂(localRestrictionMassLaw ((seq.vagueLaw ∘ φ) i)
          countSets n (a, b) : Measure NNReal) ≤ countBound n a b

  approximatingIntensity : ℕ → ℕ → FiniteMeasure ℝ
  limitIntensity : ℕ → FiniteMeasure ℝ
  lipschitzConstant : ℕ → ℝ
  lipschitzConstant_nonneg : ∀ n, 0 ≤ lipschitzConstant n
  approximating_Icc_le : ∀ i n a b, a < b →
    (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) ≤
      ENNReal.ofReal (lipschitzConstant n * (b - a))
  approximating_expectation : ∀ i n a b, a < b →
    (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) =
      ENNReal.ofReal (natCountExpectation
        (naturalRestrictionCountLaw ((seq.vagueLaw ∘ φ) i)
          countSets n (a, b)))
  limit_expectation : ∀ n a b, a < b →
    (limitIntensity n : Measure ℝ) (Set.Icc a b) =
      ENNReal.ofReal (natCountExpectation
        (naturalRestrictionCountLaw μ countSets n (a, b)))
  singleton_expectation : ∀ n x,
    ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
        (spectralEndpointFiber x) ∂(μ : Measure VagueRationalWindowState) =
      (limitIntensity n : Measure ℝ) {x}

  windowRadius : ℕ → ℝ
  windowRadius_nonneg : ∀ j, 0 ≤ windowRadius j
  bumpIndex : Type u
  closePairTest : ℕ → ℝ → bumpIndex →
    BoundedContinuousFunction (MarkedSpectralSpace Unit) NNReal
  closePairTest_covers : ∀ j a, 0 < a → ∀ x : MarkedSpectralSpace Unit,
    ∃ k, closePairTest j a k x = 1
  approximating_closePair_le : ∀ i j a, 0 < a →
    ((seq.vagueLaw ∘ φ) i : Measure VagueRationalWindowState)
        (smoothedClosePairEvent j (closePairTest j a)) ≤
      ENNReal.ofReal
        (8 * (input.C / seq.density_lower) ^ 2 * windowRadius j * a +
          16 * (input.C / seq.density_lower) ^ 2 * a ^ 2)

  validMarks : Set VagueRationalWindowState
  validMarks_closed : IsClosed validMarks
  approximatingMarks_valid : ∀ i,
    ((seq.vagueLaw ∘ φ) i : Measure VagueRationalWindowState) validMarksᶜ = 0

/-- Ambient convergence and boundary-nullness construct all restriction-law
closures used by the paper. -/
theorem ConcretePaperCountingLimitInput.countClosure
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    {input : PSSSInput.{0}} {seq : PSSSRationalWindowSequence input}
    {μ : ProbabilityMeasure VagueRationalWindowState} {φ : ℕ → ℕ}
    (c : ConcretePaperCountingLimitInput input seq μ φ) :
    NaturalRestrictionLawClosureInput atTop (seq.vagueLaw ∘ φ) μ c.countSets :=
  naturalRestrictionLawClosureInputOfAmbient _ _ c.countSets
    c.countSets_measurable c.ambient_tendsto c.countSets_boundary_null
    c.countSets_approximants_natural

/-- The full paper limit-completion structure, with scalar count-law
convergence, uniform integrability, close-pair openness, and collision
containment all proved rather than assumed. -/
def ConcretePaperCountingLimitInput.toPaperCountingLimitCompletionInput
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ)
    (c : ConcretePaperCountingLimitInput input seq μ φ) :
    PaperCountingLimitCompletionInput input seq μ φ := by
  let boundary : BoundaryRegularLimitLawInput atTop
      (seq.vagueLaw ∘ φ) μ :=
    boundaryRegularLimitLawInputOfAmbient _ _ c.consistency
      c.rational_boundary_null c.rational_approximants_natural
  let expInput := c.countClosure.toPaperCountingWeakExponentialUIInput
    (seq.vagueLaw ∘ φ) μ c.countSets c.countExponent c.countBound
    c.countExponent_pos c.countBound_nonneg c.countExp_integrable c.countExp_le
  exact paperCountingLimitCompletionInputOfWeakExponential input seq μ φ
    boundary c.approximatingIntensity c.limitIntensity c.lipschitzConstant
    c.lipschitzConstant_nonneg c.approximating_Icc_le
    (fun i n a b => naturalRestrictionCountLaw ((seq.vagueLaw ∘ φ) i)
      c.countSets n (a, b))
    (fun n a b => naturalRestrictionCountLaw μ c.countSets n (a, b))
    expInput c.approximating_expectation c.limit_expectation
    c.singleton_expectation c.windowRadius c.windowRadius_nonneg
    (fun j a => smoothedClosePairEvent j (c.closePairTest j a))
    (fun j a _ => isOpen_smoothedClosePairEvent j (c.closePairTest j a))
    localMultiplicityCollisionEvent
    (fun j a ha =>
      localMultiplicityCollisionEvent_subset_smoothedClosePairEvent j
        (c.closePairTest j a) (c.closePairTest_covers j a ha))
    c.approximating_closePair_le c.validMarks c.validMarks_closed
    c.approximatingMarks_valid

end CoareaNative.BlockBand
