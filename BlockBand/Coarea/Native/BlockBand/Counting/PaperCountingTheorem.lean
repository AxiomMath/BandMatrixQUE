module

public import BlockBand.Coarea.Native.BlockBand.Probability.IntegerCountUniformIntegrability
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockCountTransport
public import BlockBand.Coarea.Native.BlockBand.Counting.MarkedProcessTightness

/-!
# Paper-facing completion of the block-band counting argument

This module combines the strongest counting components which are presently
available without hiding any model-specific limit passage.  The physical
finite-volume estimates are obtained from a simultaneous multi-block law
transport.  The normalized unfolded laws have the concrete PSSS compact-tail
bound and hence a weak subsequence.  For each extracted subsequence,
integer-count uniform integrability supplies the previously missing intensity
passage.  Boundary regularity, close-pair event topology, and closed validity
of marks remain explicit inputs.

Consequently the final theorem gives, in one statement, all falling-factorial
orders, the physical unfolded exponential estimate, a tight vague subsequence,
almost-sure support on a consistent integer point state, collision exclusion,
and preservation of valid marks.  It assumes neither expectation convergence
nor point-state closure merely from weak convergence.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- Model-facing data which turn one extracted ambient vague limit into the
limit required by the paper.  The count-law fields are precisely the uniform-
integrability input needed to construct `CoordinateIntensityPassageInput`.
The last fields are the topological hypotheses needed for collision exclusion
and preservation of the closed mark constraint. -/
structure PaperCountingLimitCompletionInput
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState]
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ) where
  boundaryClosure :
    BoundaryRegularLimitLawInput atTop (seq.vagueLaw ∘ φ) μ
  approximatingIntensity : ℕ → ℕ → FiniteMeasure ℝ
  limitIntensity : ℕ → FiniteMeasure ℝ
  lipschitzConstant : ℕ → ℝ
  lipschitzConstant_nonneg : ∀ n, 0 ≤ lipschitzConstant n
  approximating_Icc_le :
    ∀ i n a b, a < b →
      (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) ≤
        ENNReal.ofReal (lipschitzConstant n * (b - a))
  countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ
  limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ
  countUI : ∀ n a b, a < b →
    IntegerCountExpectationConvergenceInput
      (fun i => countLaw i n a b) (limitCountLaw n a b)
  approximating_expectation :
    ∀ i n a b, a < b →
      (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) =
        ENNReal.ofReal (natCountExpectation (countLaw i n a b))
  limit_expectation :
    ∀ n a b, a < b →
      (limitIntensity n : Measure ℝ) (Set.Icc a b) =
        ENNReal.ofReal (natCountExpectation (limitCountLaw n a b))
  singleton_expectation :
    ∀ n x,
      ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
          (spectralEndpointFiber x)
        ∂(μ : Measure VagueRationalWindowState) =
      (limitIntensity n : Measure ℝ) {x}
  windowRadius : ℕ → ℝ
  windowRadius_nonneg : ∀ j, 0 ≤ windowRadius j
  closePair : ℕ → ℝ → Set VagueRationalWindowState
  closePair_open : ∀ j a, 0 < a → IsOpen (closePair j a)
  collision : ℕ → Set VagueRationalWindowState
  collision_subset_closePair : ∀ j a, 0 < a →
    collision j ⊆ closePair j a
  approximating_closePair_le : ∀ i j a, 0 < a →
    (seq.vagueLaw (φ i) : Measure VagueRationalWindowState) (closePair j a) ≤
      ENNReal.ofReal
        (8 * (input.C / seq.density_lower) ^ 2 * windowRadius j * a +
          16 * (input.C / seq.density_lower) ^ 2 * a ^ 2)
  validMarks : Set VagueRationalWindowState
  validMarks_closed : IsClosed validMarks
  approximatingMarks_valid : ∀ i,
    (seq.vagueLaw (φ i) : Measure VagueRationalWindowState) validMarksᶜ = 0

/-- Integer-count uniform integrability constructs the intensity component of
one weak-limit completion. -/
def PaperCountingLimitCompletionInput.intensityPassage
    {input : PSSSInput.{0}} {seq : PSSSRationalWindowSequence input}
    [OpensMeasurableSpace VagueRationalWindowState]
    {μ : ProbabilityMeasure VagueRationalWindowState} {φ : ℕ → ℕ}
    (completion : PaperCountingLimitCompletionInput input seq μ φ) :
    CoordinateIntensityPassageInput μ :=
  coordinateIntensityPassageInputOfIntegerCountUI μ
    completion.approximatingIntensity completion.limitIntensity
    completion.lipschitzConstant completion.lipschitzConstant_nonneg
    completion.approximating_Icc_le completion.countLaw
    completion.limitCountLaw completion.countUI
    completion.approximating_expectation completion.limit_expectation
    completion.singleton_expectation

/-- The same input gives the exact point-state completion package used by the
vague-limit closure theorem. -/
def PaperCountingLimitCompletionInput.toWeakLimitPointStateCompletionInput
    {input : PSSSInput.{0}} {seq : PSSSRationalWindowSequence input}
    [OpensMeasurableSpace VagueRationalWindowState]
    {μ : ProbabilityMeasure VagueRationalWindowState} {φ : ℕ → ℕ}
    (completion : PaperCountingLimitCompletionInput input seq μ φ) :
    WeakLimitPointStateCompletionInput (seq.vagueLaw ∘ φ) μ where
  boundaryClosure := completion.boundaryClosure
  intensityPassage := completion.intensityPassage

/-- All quantitative finite-volume statements and qualitative subsequential
limit conclusions belonging to the paper's counting theorem. -/
structure PaperCountingTheoremConclusion
    (input : PSSSInput.{0})
    (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState]
    [TopologicalSpace (ProbabilityMeasure VagueRationalWindowState)]
    {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μphys : Measure Ω) (ν : Measure Ξ)
    (p : Params)
    (G : BlockGUE.Law.{0} (GaussianRing.physicalBlockSizes p)
      (GaussianRing.physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix
      (BlockGUE.Index (GaussianRing.physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (transport : GaussianRing.PhysicalMultiBlockCountTransport
      μphys ν p G A₀ N)
    (e L ρ : ℝ) where
  physicalFactorial : ∀ a b, a ≤ b → ∀ r, 1 ≤ r →
    ∫ ω, ((N a b ω).descFactorial r : ℝ) ∂μphys ≤
      ((input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)) ^ r
  physicalUnfoldedExponential : ∀ R t, 0 ≤ R → 0 ≤ t →
    ∫ ω, Real.exp (t *
      (GaussianRing.transportedUnfoldedIntervalCount N e L ρ R ω : ℝ)) ∂μphys ≤
      Real.exp (2 * R * ((input.C / Real.sqrt p.c) / ρ) *
        (Real.exp t - 1))
  normalizedFactorial : ∀ i a b, a ≤ b → ∀ r, 1 ≤ r →
    ∫ ω, ((BlockGUE.intervalCount (seq.model i) (seq.deformation i)
      (Set.Icc a b) ω).descFactorial r : ℝ) ∂(seq.model i).P ≤
      (input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) * (b - a)) ^ r
  normalizedUnfoldedExponential : ∀ i R t, 0 ≤ R → 0 ≤ t →
    ∫ ω, Real.exp (t *
      (BlockGUE.unfoldedIntervalCount (seq.model i) (seq.deformation i)
        (seq.energy i) (seq.scale i) (seq.density i) R ω : ℝ))
      ∂(seq.model i).P ≤
      Real.exp (2 * R * (input.C / seq.density i) * (Real.exp t - 1))
  compactTail : ∀ i m n,
    (seq.vagueLaw i : Measure VagueRationalWindowState)
      {ν | (psssRationalWindowMassCap seq m n : ENNReal) <
        ((ν n).mass : ENNReal)} ≤
      psssRationalWindowTailSchedule m n
  completedSubsequence :
    ∃ (μ : ProbabilityMeasure VagueRationalWindowState)
      (φ : ℕ → ℕ) (s : ℝ)
      (completion : PaperCountingLimitCompletionInput input seq μ φ),
      StrictMono φ ∧
      Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) ∧
      Dense (shiftedRationalEndpoints s) ∧
      (shiftedRationalEndpoints s).Countable ∧
      (∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        HasNullMarkedWindowBoundaries ν ∧
        HasNullLocalRestrictionBoundaries
          (shiftedRationalDeterminingFamily s) ν ∧
        ∃ ξ : ShiftedRationalWindowPointState s, ξ.1 = ν) ∧
      (∀ j a, 0 < a →
        (μ : Measure VagueRationalWindowState) (completion.closePair j a) ≤
          ENNReal.ofReal
            (8 * (input.C / seq.density_lower) ^ 2 *
                completion.windowRadius j * a +
              16 * (input.C / seq.density_lower) ^ 2 * a ^ 2)) ∧
      (∀ j, (μ : Measure VagueRationalWindowState)
        (completion.collision j) = 0) ∧
      (μ : Measure VagueRationalWindowState) completion.validMarksᶜ = 0

/-- **Paper-facing counting theorem.**  A simultaneous physical block-law
transport proves every finite-volume factorial and exponential estimate.
PSSS compact tails then produce an ambient vague subsequence.  The
last hypothesis is applied only after that subsequence is known; its
integer-count uniform-integrability fields construct intensity passage, while
its boundary, collision-event, and closed-mark fields complete the limit.

The constant in the physical conclusions is exactly
`input.C / sqrt p.c`, and the collision bound uses the uniform unfolded
constant `input.C / seq.density_lower`. -/
theorem paperCountingTheorem
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    [HasOuterApproxClosed VagueRationalWindowState]
    (input : PSSSInput.{0})
    (seq : PSSSRationalWindowSequence input)
    {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μphys : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μphys] [IsProbabilityMeasure ν]
    (p : Params)
    (G : BlockGUE.Law.{0} (GaussianRing.physicalBlockSizes p)
      (GaussianRing.physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix
      (BlockGUE.Index (GaussianRing.physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (transport : GaussianRing.PhysicalMultiBlockCountTransport
      μphys ν p G A₀ N)
    (e L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hdim : (p.n * p.W : ℝ) ≤ L)
    (complete : ∀ (μ : ProbabilityMeasure VagueRationalWindowState)
      (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) →
      PaperCountingLimitCompletionInput input seq μ φ) :
    PaperCountingTheoremConclusion input seq μphys ν p G A₀ N transport e L ρ := by
  refine
    { physicalFactorial := ?_
      physicalUnfoldedExponential := ?_
      normalizedFactorial := ?_
      normalizedUnfoldedExponential := ?_
      compactTail := ?_
      completedSubsequence := ?_ }
  · intro a b hab r hr
    exact transport.factorialCount input μphys ν G A₀ N hab r hr
  · intro R t hR ht
    exact transport.unfoldedCountExponential input μphys ν G A₀ N
      e L ρ R t hL hρ hR hdim ht
  · intro i a b hab r hr
    exact psss_factorialCount input (seq.hd i) (seq.model i)
      (seq.deformation i) a b hab r hr
  · intro i R t hR ht
    exact psss_unfoldedCountExponential input (seq.hd i) (seq.model i)
      (seq.deformation i) (seq.energy i) (seq.scale i) (seq.density i)
      R t (seq.scale_pos i) (seq.density_pos i) hR
      (seq.dimension_le_scale i) ht
  · intro i m n
    exact seq.vague_mass_tail i m n
  · obtain ⟨μ, φ, hφ, hlim⟩ := seq.exists_vague_weak_subsequence
    let completion := complete μ φ hφ hlim
    obtain ⟨s, hdense, hcountable, hae⟩ :=
      completion.toWeakLimitPointStateCompletionInput.exists_shift_ae_lifts_toPointState
    have hclosePair : ∀ j a, 0 < a →
        (μ : Measure VagueRationalWindowState) (completion.closePair j a) ≤
          ENNReal.ofReal
            (8 * (input.C / seq.density_lower) ^ 2 *
                completion.windowRadius j * a +
              16 * (input.C / seq.density_lower) ^ 2 * a ^ 2) := by
      intro j a ha
      exact limit_closePairEvent_le_manuscript hlim
        (completion.closePair j) (completion.closePair_open j) ha
        (fun i => completion.approximating_closePair_le i j a ha)
    have hcollision : ∀ j,
        (μ : Measure VagueRationalWindowState) (completion.collision j) = 0 := by
      intro j
      let scale : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
      apply measure_limitCollision_eq_zero hlim
        (completion.closePair j) (completion.collision j)
        (completion.closePair_open j)
        (completion.collision_subset_closePair j)
        scale (R := completion.windowRadius j)
        (K := input.C / seq.density_lower)
      · intro n
        dsimp [scale]
        positivity
      · have hscale : Tendsto
            (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [scale, div_eq_mul_inv] using hscale
      · intro n i
        exact completion.approximating_closePair_le i j (scale n) (by
          dsimp [scale]
          positivity)
    have hmarks : (μ : Measure VagueRationalWindowState)
        completion.validMarksᶜ = 0 :=
      measure_compl_closed_eq_zero_of_tendsto hlim
        completion.validMarks completion.validMarks_closed
        completion.approximatingMarks_valid
    exact ⟨μ, φ, s, completion, hφ, hlim, hdense, hcountable,
      hae, hclosePair, hcollision, hmarks⟩

end CoareaNative.BlockBand
