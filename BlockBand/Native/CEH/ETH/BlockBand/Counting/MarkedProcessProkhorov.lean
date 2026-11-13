module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.CountingTheorem
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Sequences

/-!
# Tightness and subsequence existence from compact containment

The proof of the counting theorem concludes by invoking tightness of marked point measures.  The quantitative count estimates alone
do not define the vague marked-configuration topology, so they cannot by
themselves manufacture compact subsets of that space.  This module isolates
that topology-specific step as an explicit compact-containment hypothesis and then carries out
the Mathlib tightness and Prokhorov steps.

The first theorem turns a compact exhaustion with uniformly vanishing
complement mass into `IsTightMeasureSet`.  The second specializes it to the
usual Markov form `C / m` obtained from local-count tails, provided the
complement of the compact set is contained in the large-count event.  The
last theorems apply Mathlib's Prokhorov compactness theorem and extract a
weakly convergent subsequence.

To apply this to the marked process one needs a Hausdorff Borel configuration space in which the
sets imposing bounded counts on sufficiently many compact spectral windows (with marks in the
compact mark space) are compact, together with the displayed complement containment. No such
topology is postulated here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory Filter
open scoped Topology

universe u

/-- An explicit compact exhaustion with uniformly vanishing complement mass
makes a family of probability measures tight. -/
theorem isTightMeasureSet_range_of_compact_exhaustion
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μs : ι → ProbabilityMeasure X)
    (K : ℕ → Set X) (hK : ∀ m, IsCompact (K m))
    (u : ℕ → ENNReal) (hu : Tendsto u atTop (𝓝 0))
    (hbound : ∀ i m, (μs i : Measure X) (K m)ᶜ ≤ u m) :
    IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ μs)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hev : ∀ᶠ m in atTop, u m ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hu) ε hε
  obtain ⟨m, hm⟩ := hev.exists
  refine ⟨K m, hK m, ?_⟩
  intro ν hν
  rcases hν with ⟨i, rfl⟩
  exact (hbound i m).trans hm

/-- Local-count Markov tails imply tightness once bounded-count sets have a
compact-containment realization.  The finiteness of `C` is essential for
`C / m → 0`. -/
theorem isTightMeasureSet_range_of_localCount_compactContainment
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μs : ι → ProbabilityMeasure X)
    (localCount : X → ENNReal) (K : ℕ → Set X)
    (hK : ∀ m, IsCompact (K m))
    (hcontain : ∀ m, (K m)ᶜ ⊆ {x | (m : ENNReal) ≤ localCount x})
    (C : ENNReal) (hC : C ≠ ⊤)
    (htail : ∀ i m, (μs i : Measure X)
      {x | (m : ENNReal) ≤ localCount x} ≤ C / (m : ENNReal)) :
    IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ μs)) := by
  have hdiv : Tendsto (fun m : ℕ => C / (m : ENNReal)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr hC)
  apply isTightMeasureSet_range_of_compact_exhaustion μs K hK
    (fun m => C / (m : ENNReal)) hdiv
  intro i m
  exact (measure_mono (hcontain m)).trans (htail i m)

/-- Prokhorov compactness for a tight family of probability measures, stated
in the exact coercion shape used by Mathlib. -/
theorem isCompact_closure_range_of_isTight
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [BorelSpace X]
    (μs : ι → ProbabilityMeasure X)
    (htight : IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ μs))) :
    IsCompact (closure (Set.range μs)) := by
  apply isCompact_closure_of_isTightMeasureSet
  have heq :
      {ν : Measure X | ∃ μ ∈ Set.range μs, (μ : Measure X) = ν} =
        Set.range (ProbabilityMeasure.toMeasure ∘ μs) := by
    ext ν
    constructor
    · rintro ⟨μ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨μs i, ⟨i, rfl⟩, rfl⟩
  rw [heq]
  exact htight

/-- A tight sequence of probability measures has a weakly convergent subsequence.  `FirstCountableTopology (ProbabilityMeasure X)` is
kept explicit because subsequence extraction from compactness is sequential
only under this hypothesis. -/
theorem exists_weaklyConvergent_subsequence_of_isTight
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [BorelSpace X]
    [FirstCountableTopology (ProbabilityMeasure X)]
    (μs : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ μs))) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  have hcompact : IsCompact (closure (Set.range μs)) :=
    isCompact_closure_range_of_isTight μs htight
  obtain ⟨μ, hμ, φ, hφ, hlim⟩ := hcompact.tendsto_subseq fun n =>
    subset_closure ⟨n, rfl⟩
  exact ⟨μ, φ, hφ, hlim⟩

/-- Combined compact-containment-to-subsequence theorem in the form needed by
the marked process.  Unlike `CountingTheoremInput`, this theorem does not
assume a weak limit: it produces one from concrete compact sets and the
uniform local-count tail. -/
theorem exists_weaklyConvergent_subsequence_of_localCount_tail
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [BorelSpace X]
    [FirstCountableTopology (ProbabilityMeasure X)]
    (μs : ℕ → ProbabilityMeasure X)
    (localCount : X → ENNReal) (K : ℕ → Set X)
    (hK : ∀ m, IsCompact (K m))
    (hcontain : ∀ m, (K m)ᶜ ⊆ {x | (m : ENNReal) ≤ localCount x})
    (C : ENNReal) (hC : C ≠ ⊤)
    (htail : ∀ i m, (μs i : Measure X)
      {x | (m : ENNReal) ≤ localCount x} ≤ C / (m : ENNReal)) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_of_isTight μs
  exact isTightMeasureSet_range_of_localCount_compactContainment
    μs localCount K hK hcontain C hC htail

end CEHNative.BlockBand
