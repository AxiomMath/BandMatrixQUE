
module

public import BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoDensityClosure
public import Mathlib.MeasureTheory.PiSystem

/-!
# Adapted rectangles generate predictable L²

This module gives the set-theoretic core of the density of adapted rectangles.  It proves
that the predictable generators form a π-system and classifies each generator as either
an adapted rectangle or a time-zero face, the latter being null for `dt × P`.  The
λ-system closure (stability of closed-span indicator membership under complements and
countable disjoint unions) is `ContinuousItoPredictableLambdaSystemClosure.indicatorDynkinSystem`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoAdaptedRectangleDensity

open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open ContinuousIto
open ContinuousItoDensityClosure

/-- The standard predictable rectangles are closed under nonempty intersections. -/
theorem predictableGenerators_isPiSystem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) : IsPiSystem (predictableGenerators ℱ) := by
  intro S hS U hU hne
  rcases hS with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · rcases hU with ⟨B, hB, rfl⟩ | ⟨u, v, B, hB, rfl⟩
    · left
      refine ⟨A ∩ B, hA.inter hB, ?_⟩
      ext x
      simp [and_assoc, and_left_comm, and_comm]
    · exfalso
      rcases hne with ⟨x, hx⟩
      simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hx
      have hu0 : (0 : ℝ) ≤ (u : ℝ) := by positivity
      linarith
  · rcases hU with ⟨B, hB, rfl⟩ | ⟨u, v, B, hB, rfl⟩
    · exfalso
      rcases hne with ⟨x, hx⟩
      simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hx
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
      linarith
    · right
      let a : ℝ≥0 := max s u
      refine ⟨a, min t v, A ∩ B, ?_, ?_⟩
      · apply (ℱ.mono_space (le_max_left s u)) A hA |>.inter
        exact (ℱ.mono_space (le_max_right s u)) B hB
      · ext x
        simp only [mem_inter_iff, mem_prod, mem_Ioc]
        dsimp only [a]
        simp only [NNReal.coe_max, max_lt_iff, le_min_iff]
        aesop

/-- Every positive-length predictable rectangle generator already has its indicator in
 the elementary span; the real upper endpoint in `predictableGenerators` is converted
 to a nonnegative endpoint only in the nonempty case. -/
theorem intervalGenerator_indicator_mem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [IsFiniteMeasure (timeProbMeasure T P)] {s : ℝ≥0} {t : ℝ} {A : Set Ω}
    (hA : MeasurableSet[ℱ.space s] A) :
    predictableIndicatorL2 ℱ T P
      (measurableSet_predictableRectangle ℱ (t := ⟨max t 0, le_max_right _ _⟩) hA) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
  exact (elementaryPredictableSubmodule ℱ T P).le_topologicalClosure
    (elementaryPredictableL2_mem_submodule ℱ T P
      (t := ⟨max t 0, le_max_right _ _⟩) hA 1)

/-- The only generator not of the form of an adapted interval is the
 time-zero face.  Under the product measure it is null. -/
theorem zeroFace_measure_zero {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (P : Measure Ω) [SFinite P] (A : Set Ω) :
    timeProbMeasure T P (({0} : Set ℝ) ×ˢ A) = 0 := by
  unfold timeProbMeasure
  rw [Measure.prod_prod]
  simp

/-- Every predictable generator is either a time-zero face or an adapted
 rectangle with nonnegative upper endpoint.  Empty negative-endpoint intervals are
 represented by the empty adapted interval `(0,0] × univ`. -/
theorem predictableGenerator_classification {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (S : Set (ℝ × Ω))
    (hS : S ∈ predictableGenerators ℱ) :
    (∃ A, MeasurableSet[ℱ.space 0] A ∧ S = ({0} : Set ℝ) ×ˢ A) ∨
      ∃ s t : ℝ≥0, ∃ A, MeasurableSet[ℱ.space s] A ∧
        S = Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A := by
  rcases hS with hzero | ⟨s, t, A, hA, rfl⟩
  · exact Or.inl hzero
  · right
    by_cases ht : 0 ≤ t
    · exact ⟨s, ⟨t, ht⟩, A, hA, rfl⟩
    · refine ⟨0, 0, Set.univ, MeasurableSet.univ, ?_⟩
      ext x
      simp only [mem_prod, mem_Ioc, mem_univ, and_true]
      constructor
      · intro hx
        have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
        linarith
      · intro hx
        linarith

/-- Consequently every predictable generator is an adapted rectangle or the null time-zero
 face. -/
theorem predictableGenerator_is_zeroFace_or_elementary {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] (S : Set (ℝ × Ω)) (hS : S ∈ predictableGenerators ℱ) :
    (∃ A, MeasurableSet[ℱ.space 0] A ∧
      S = ({0} : Set ℝ) ×ˢ A ∧ timeProbMeasure T P S = 0) ∨
      ∃ s t : ℝ≥0, ∃ A, MeasurableSet[ℱ.space s] A ∧
        S = Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A := by
  rcases predictableGenerator_classification ℱ S hS with
    ⟨A, hA, rfl⟩ | hrect
  · left
    exact ⟨A, hA, rfl, zeroFace_measure_zero T P A⟩
  · exact Or.inr hrect

end BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoAdaptedRectangleDensity
