module

public import BlockBand.Coarea.Native.BlockBand.Counting.PaperCountingConcreteTheorem

/-!
# Unit-mark specialization of the concrete counting limit

The presently formalized BlockGUE configurations carry the trivial
`Unit` mark.  Therefore mark validity is automatic: the valid carrier is the
whole vague state space.  Ambient convergence is already a field of the
consistency package and need not be repeated.  This module removes both
hypotheses from the concrete paper input.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
universe u

structure UnitMarkedPaperCountingLimitInput
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState]
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ) where
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

/-- Every measurable restriction of a finite local counting coordinate has
natural mass, not merely the original rational determining restrictions. -/
theorem finiteMarkedLocalWindowEncoding_restrict_mass_mem_range_any
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) (n : ℕ)
    {S : Set (MarkedSpectralSpace Unit)} (hS : MeasurableSet S) :
    ((finiteMarkedLocalWindowEncoding x n).restrict S).mass ∈
      Set.range ((↑) : ℕ → NNReal) := by
  let T := S ∩ markedSpectralWindow Unit n
  have hT : MeasurableSet T :=
    hS.inter (measurableSet_markedSpectralWindow Unit n)
  have hmass :
      ((finiteMarkedLocalWindowEncoding x n).restrict S).mass =
        ((finiteMarkedCountingMeasure x).restrict T).mass := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
    change ((((finiteMarkedCountingMeasure x : Measure _).restrict
      (markedSpectralWindow Unit n)).restrict S) Set.univ) =
        ((finiteMarkedCountingMeasure x : Measure _).restrict T) Set.univ
    rw [Measure.restrict_restrict hS]
  rw [hmass]
  exact finiteMarkedCountingMeasure_restrict_mass_mem_range x hT

/-- Consequently every unfolded finite BlockGUE configuration has
natural local masses for every measurable determining family. -/
theorem BlockGUE.unfoldedVagueRationalWindowState_natural
    {κ : Type u} {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n q, MeasurableSet (sets n q)) (ω : M.Ω) :
    HasNaturalLocalRestrictionMass sets
      (BlockGUE.unfoldedVagueRationalWindowState M A₀ e L ρ ω) := by
  intro n q
  exact finiteMarkedLocalWindowEncoding_restrict_mass_mem_range_any
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω) n (hsets n q)

/-- Fill the full concrete input, taking the valid Unit-mark carrier to be the
whole state space and reusing ambient convergence from consistency. -/
def UnitMarkedPaperCountingLimitInput.toConcrete
    [OpensMeasurableSpace VagueRationalWindowState]
    {input : PSSSInput.{0}} {seq : PSSSRationalWindowSequence input}
    {μ : ProbabilityMeasure VagueRationalWindowState} {φ : ℕ → ℕ}
    (c : UnitMarkedPaperCountingLimitInput input seq μ φ) :
    ConcretePaperCountingLimitInput input seq μ φ where
  ambient_tendsto := c.consistency.ambient_law_tendsto
  consistency := c.consistency
  rational_boundary_null := c.rational_boundary_null
  rational_approximants_natural := c.rational_approximants_natural
  countSets := c.countSets
  countSets_measurable := c.countSets_measurable
  countSets_boundary_null := c.countSets_boundary_null
  countSets_approximants_natural := c.countSets_approximants_natural
  countExponent := c.countExponent
  countBound := c.countBound
  countExponent_pos := c.countExponent_pos
  countBound_nonneg := c.countBound_nonneg
  countExp_integrable := c.countExp_integrable
  countExp_le := c.countExp_le
  approximatingIntensity := c.approximatingIntensity
  limitIntensity := c.limitIntensity
  lipschitzConstant := c.lipschitzConstant
  lipschitzConstant_nonneg := c.lipschitzConstant_nonneg
  approximating_Icc_le := c.approximating_Icc_le
  approximating_expectation := c.approximating_expectation
  limit_expectation := c.limit_expectation
  singleton_expectation := c.singleton_expectation
  windowRadius := c.windowRadius
  windowRadius_nonneg := c.windowRadius_nonneg
  bumpIndex := c.bumpIndex
  closePairTest := c.closePairTest
  closePairTest_covers := c.closePairTest_covers
  approximating_closePair_le := c.approximating_closePair_le
  validMarks := Set.univ
  validMarks_closed := isClosed_univ
  approximatingMarks_valid := fun i => by simp

/-- Unit-mark data give the complete paper limit package with no separate mark
closure or ambient-convergence hypothesis. -/
def UnitMarkedPaperCountingLimitInput.toPaperCountingLimitCompletionInput
    [OpensMeasurableSpace VagueRationalWindowState]
    [HasOuterApproxClosed VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ)
    (c : UnitMarkedPaperCountingLimitInput input seq μ φ) :
    PaperCountingLimitCompletionInput input seq μ φ :=
  c.toConcrete.toPaperCountingLimitCompletionInput input seq μ φ

end CoareaNative.BlockBand
