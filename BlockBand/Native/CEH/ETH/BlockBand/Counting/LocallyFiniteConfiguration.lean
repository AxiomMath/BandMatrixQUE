module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.MarkedConfigurationSpace
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# A common local-window state space for varying finite configurations

Mathlib does not currently bundle locally finite integer-valued measures with
the vague topology.  This module therefore constructs a common
ambient space which retains exactly the local data used by vague convergence:
a sequence of finite measures, one for every bounded window.  Finite marked
configurations of *any* size map into this same space by restricting their
counting measure to the windows `[-n,n] × Mark`.

The ambient space uses Mathlib's weak topology on each `FiniteMeasure` and the
countable product topology.  It is Hausdorff (and carries the product Borel
structure under the standard countability hypotheses).  We prove the key
compact-containment fact: coordinatewise mass bounds together with compact
support in each window form a compact subset of the common space.

A predicate records projective consistency of the window restrictions.  This
module does not identify this ambient product, or its consistency locus, with the
paper's space of locally finite point measures; this would further require
closedness of consistency, integer-valuedness of limits, and the identification
of the induced topology with vague convergence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

universe u

/-- The marked spectral base space. -/
abbrev MarkedSpectralSpace (Mark : Type u) := ℝ × Mark

/-- A common state space for local-window measure data.  Coordinate `n` is a
finite measure carrying the configuration seen in a bounded window. -/
abbrev LocalWindowMeasureEncoding (Mark : Type u) [MeasurableSpace Mark] :=
  ℕ → FiniteMeasure (MarkedSpectralSpace Mark)

/-- The standard closed spectral window of radius `n`, with unrestricted
marks. -/
def markedSpectralWindow (Mark : Type u) (n : ℕ) :
    Set (MarkedSpectralSpace Mark) :=
  Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ Set.univ

/-- Standard marked spectral windows are measurable. -/
theorem measurableSet_markedSpectralWindow
    (Mark : Type u) [MeasurableSpace Mark] (n : ℕ) :
    MeasurableSet (markedSpectralWindow Mark n) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- A finite labeled configuration defines a finite counting measure on the
marked spectral space. -/
def finiteMarkedCountingMeasure
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (x : FiniteMarkedConfiguration N Mark) :
    FiniteMeasure (MarkedSpectralSpace Mark) :=
  ⟨∑ i, Measure.dirac (x i), inferInstance⟩

/-- The finite counting measure has mass equal to the number of labels. -/
theorem finiteMarkedCountingMeasure_mass
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (x : FiniteMarkedConfiguration N Mark) :
    (finiteMarkedCountingMeasure x).mass = N := by
  simp [finiteMarkedCountingMeasure, FiniteMeasure.mass]

/-- Restricting the counting measure to every standard bounded window embeds
finite configurations of arbitrary sizes into one common target type. -/
def finiteMarkedLocalWindowEncoding
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (x : FiniteMarkedConfiguration N Mark) :
    LocalWindowMeasureEncoding Mark :=
  fun n => (finiteMarkedCountingMeasure x).restrict
    (markedSpectralWindow Mark n)

/-- Successive coordinates in a local-window encoding agree after
restriction to the smaller window. -/
def IsConsistentLocalWindowEncoding
    {Mark : Type u} [MeasurableSpace Mark]
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ m n, m ≤ n →
    (ν n).restrict (markedSpectralWindow Mark m) = ν m

/-- The encoding of every finite configuration is projectively consistent. -/
theorem finiteMarkedLocalWindowEncoding_consistent
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (x : FiniteMarkedConfiguration N Mark) :
    IsConsistentLocalWindowEncoding
      (finiteMarkedLocalWindowEncoding x) := by
  intro m n hmn
  unfold finiteMarkedLocalWindowEncoding
  ext s hs
  change ((finiteMarkedCountingMeasure x : Measure (MarkedSpectralSpace Mark)).restrict
      (markedSpectralWindow Mark n)).restrict (markedSpectralWindow Mark m) s =
    (finiteMarkedCountingMeasure x : Measure (MarkedSpectralSpace Mark)).restrict
      (markedSpectralWindow Mark m) s
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    Measure.restrict_apply (hs.inter (measurableSet_markedSpectralWindow Mark m))]
  congr 1
  apply Set.inter_eq_left.2
  intro z hz
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact ⟨⟨by
    exact le_trans (show -(n : ℝ) ≤ -(m : ℝ) by linarith) hz.2.1.1,
    le_trans hz.2.1.2 hmn'⟩, Set.mem_univ z.2⟩

/-- Coordinatewise compact support and mass bounds in the common local-window
space. -/
def localWindowCompactContainment
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark)) :
    Set (LocalWindowMeasureEncoding Mark) :=
  Set.pi Set.univ fun n =>
    {μ : FiniteMeasure (MarkedSpectralSpace Mark) |
      μ.mass ≤ C n ∧ μ (K n)ᶜ = 0}

/-- The fundamental compact-containment fact for the local-window encoding.
It is a direct countable-product assembly of Mathlib's compactness theorem for
finite measures of bounded mass supported on a compact set. -/
theorem isCompact_localWindowCompactContainment
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark))
    (hK : ∀ n, IsCompact (K n)) :
    IsCompact (localWindowCompactContainment C K) := by
  apply isCompact_univ_pi
  intro n
  exact isCompact_setOfPred_finiteMeasure_le_of_isCompact (C n) (hK n)

/-- A sequence whose local-window encodings obey one family of compact
support and mass bounds has a convergent subsequence in the product weak
topology.  This is the deterministic compactness core of the desired
point-process argument; it does not assert that the limit remains
integer-valued or projectively consistent. -/
theorem exists_tendsto_subseq_localWindowCompactContainment
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [FirstCountableTopology (LocalWindowMeasureEncoding Mark)]
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark))
    (hK : ∀ n, IsCompact (K n))
    (ν : ℕ → LocalWindowMeasureEncoding Mark)
    (hν : ∀ q, ν q ∈ localWindowCompactContainment C K) :
    ∃ νlim ∈ localWindowCompactContainment C K,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 νlim) := by
  exact (isCompact_localWindowCompactContainment C K hK).tendsto_subseq hν

/-- Evaluation at a fixed window is continuous for the product weak topology. -/
theorem continuous_localWindowMeasureEvaluation
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)] (n : ℕ) :
    Continuous (fun ν : LocalWindowMeasureEncoding Mark => ν n) :=
  continuous_apply n

/-- The common local-window space is Hausdorff whenever the mark space is. -/
theorem localWindowMeasureEncoding_t2
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)] :
    T2Space (LocalWindowMeasureEncoding Mark) := by
  infer_instance

/-- Membership in the compact-containment set is exactly the family of local
mass and support conditions. -/
theorem mem_localWindowCompactContainment_iff
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    {C : ℕ → NNReal} {K : ℕ → Set (MarkedSpectralSpace Mark)}
    (ν : LocalWindowMeasureEncoding Mark) :
    ν ∈ localWindowCompactContainment C K ↔
      ∀ n, (ν n).mass ≤ C n ∧ ν n (K n)ᶜ = 0 := by
  simp [localWindowCompactContainment]

/-- Compact mark sets give compact marked spectral windows. -/
theorem isCompact_markedSpectralWindow_inter_marks
    {Mark : Type u} [TopologicalSpace Mark]
    (n : ℕ) {D : Set Mark} (hD : IsCompact D) :
    IsCompact (Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ D) :=
  isCompact_Icc.prod hD

end CEHNative.BlockBand
