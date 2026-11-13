module

public import BlockBand.Coarea.Native.BlockBand.Counting.MarkedProcessProkhorov

/-!
# A finite marked-configuration precursor

The paper uses the vague topology on locally finite marked point
measures.  Mathlib has weak topologies for finite and probability
measures, but no bundled space of locally finite integer-valued measures with
its vague topology.  This module therefore constructs a concrete precursor: a fixed-size,
labeled configuration is a function `Fin N → ℝ × Mark` with the product
Borel topology.

For this space we prove that local-count superlevel events over open spectral
windows are open (hence Borel), and that requiring every spectral coordinate
to lie in a bounded interval and every mark to lie in a fixed compact set is
compact.  We then instantiate the compact-exhaustion Prokhorov theorem for a
sequence of laws on this fixed-size space, under the exact uniform escape-tail
hypothesis needed for these compact sets.

This does **not** construct the paper's limit state space.  In
particular, fixed `N` labeled products cannot represent configurations with
arbitrarily many points, and local-count bounds on bounded windows do not
control labeled points escaping to infinity.  The space of locally finite
marked point measures with the vague topology is `BlockBand.MarkedPointMeasure`;
tightness of the physical marked laws there is
`BlockBand.Counting.criticalSequence_markedLaws_isTight`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology

universe u

/-- A fixed-size labeled marked configuration.  The first component is the
rescaled spectral location and the second is its mark. -/
abbrev FiniteMarkedConfiguration (N : ℕ) (Mark : Type u) :=
  Fin N → ℝ × Mark

/-- The number of labeled points whose spectral coordinate lies in `U`. -/
def finiteMarkedLocalCount {N : ℕ} {Mark : Type u}
    (U : Set ℝ) (x : FiniteMarkedConfiguration N Mark) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => (x i).1 ∈ U).card

/-- The event that at least `m` labeled points have spectral coordinate in
`U`. -/
def finiteMarkedCountGE {N : ℕ} {Mark : Type u}
    (U : Set ℝ) (m : ℕ) : Set (FiniteMarkedConfiguration N Mark) :=
  {x | m ≤ finiteMarkedLocalCount U x}

/-- For an open spectral window, the event that its local count is at least a
fixed integer is open in the finite product topology. -/
theorem isOpen_finiteMarkedCountGE
    {N : ℕ} {Mark : Type u} [TopologicalSpace Mark]
    {U : Set ℝ} (hU : IsOpen U) (m : ℕ) :
    IsOpen (finiteMarkedCountGE (N := N) (Mark := Mark) U m) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change m ≤ (Finset.univ.filter fun i => (x i).1 ∈ U).card at hx
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hx
  let V : Set (FiniteMarkedConfiguration N Mark) :=
    ⋂ i ∈ s, {y | (y i).1 ∈ U}
  have hVopen : IsOpen V := by
    exact isOpen_biInter_finset fun i _ =>
      hU.preimage (continuous_fst.comp (continuous_apply i))
  refine mem_of_superset (hVopen.mem_nhds ?_) ?_
  · simp only [V, Set.mem_iInter, Set.mem_ofPred_eq]
    intro i hi
    exact Finset.mem_filter.mp (hs hi) |>.2
  · intro y hy
    have hy' : ∀ i ∈ s, (y i).1 ∈ U := by
      simpa only [V, Set.mem_iInter, Set.mem_ofPred_eq] using hy
    change m ≤ (Finset.univ.filter fun i => (y i).1 ∈ U).card
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hy' i hi⟩

/-- Open-window local-count superlevel events are Borel measurable in the
canonical product Borel structure. -/
theorem measurableSet_finiteMarkedCountGE
    {N : ℕ} {Mark : Type u} [TopologicalSpace Mark]
    [MeasurableSpace Mark] [BorelSpace Mark] [SecondCountableTopology Mark]
    {U : Set ℝ} (hU : IsOpen U) (m : ℕ) :
    MeasurableSet (finiteMarkedCountGE (N := N) (Mark := Mark) U m) :=
  (isOpen_finiteMarkedCountGE (Mark := Mark) hU m).measurableSet

/-- Configurations all of whose spectral coordinates lie in `[-R,R]` and all
of whose marks lie in `C`. -/
def finiteMarkedCompactSet {N : ℕ} {Mark : Type u}
    (R : ℝ) (C : Set Mark) : Set (FiniteMarkedConfiguration N Mark) :=
  Set.pi Set.univ fun _ => Set.Icc (-R) R ×ˢ C

/-- Bounded spectral coordinates and compact marks form a compact set in the
fixed finite product topology. -/
theorem isCompact_finiteMarkedCompactSet
    {N : ℕ} {Mark : Type u} [TopologicalSpace Mark]
    (R : ℝ) {C : Set Mark} (hC : IsCompact C) :
    IsCompact (finiteMarkedCompactSet (N := N) R C) := by
  exact isCompact_univ_pi fun _ => isCompact_Icc.prod hC

/-- Exact complement description for the finite compact-containment sets.
Leaving such a set means that some labeled spectral coordinate escapes the
bounded interval or its mark escapes the chosen compact mark set. -/
theorem mem_compl_finiteMarkedCompactSet_iff
    {N : ℕ} {Mark : Type u} [TopologicalSpace Mark]
    {R : ℝ} {C : Set Mark} (x : FiniteMarkedConfiguration N Mark) :
    x ∈ (finiteMarkedCompactSet (N := N) R C)ᶜ ↔
      ∃ i, (x i).1 ∉ Set.Icc (-R) R ∨ (x i).2 ∉ C := by
  simp only [finiteMarkedCompactSet, Set.mem_compl_iff, Set.mem_pi,
    Set.mem_univ, true_implies, Set.mem_prod, not_forall, not_and_or]

/-- A concrete Prokhorov subsequence theorem for fixed-size labeled marked
configurations.  The hypothesis is the compact-containment estimate:
uniformly in the law, the probability that a spectral coordinate leaves
`[-R m,R m]` or a mark leaves `C m` is bounded by `u m → 0`.

This theorem is a finite-configuration instantiation of
`isTightMeasureSet_range_of_compact_exhaustion`; it deliberately does not
pretend that bounded local counts alone imply the displayed escape estimate. -/
theorem exists_weaklyConvergent_subsequence_finiteMarkedConfiguration
    {N : ℕ} {Mark : Type u}
    [TopologicalSpace Mark] [MeasurableSpace Mark]
    [T2Space Mark] [BorelSpace Mark] [SecondCountableTopology Mark]
    [FirstCountableTopology
      (ProbabilityMeasure (FiniteMarkedConfiguration N Mark))]
    (μs : ℕ → ProbabilityMeasure (FiniteMarkedConfiguration N Mark))
    (R : ℕ → ℝ) (C : ℕ → Set Mark) (hC : ∀ m, IsCompact (C m))
    (u : ℕ → ENNReal) (hu : Tendsto u atTop (𝓝 0))
    (hescape : ∀ i m, (μs i : Measure (FiniteMarkedConfiguration N Mark))
      (finiteMarkedCompactSet (N := N) (R m) (C m))ᶜ ≤ u m) :
    ∃ μ : ProbabilityMeasure (FiniteMarkedConfiguration N Mark),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_of_isTight μs
  apply isTightMeasureSet_range_of_compact_exhaustion μs
    (fun m => finiteMarkedCompactSet (N := N) (R m) (C m))
    (fun m => isCompact_finiteMarkedCompactSet (R m) (hC m)) u hu
  exact hescape

end CoareaNative.BlockBand
