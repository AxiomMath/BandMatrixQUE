module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.IntegerPointMeasureClosure
public import BlockBand.Native.CEH.ETH.BlockBand.Counting.MarkedProcessProkhorov

/-!
# Bundled local point-measure state space

This is the strongest state space currently justified by the local-window
construction: consistent finite window measures whose masses on an explicit
countable determining family are natural numbers.  It inherits the product
weak topology.  We do not identify this topology with a canonical vague
topology on locally finite point measures.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u v

/-- Bundled consistent local-window encodings with integer masses on the
chosen local determining family. -/
abbrev LocalPointMeasureStateSpace
    (Mark : Type u) [MeasurableSpace Mark]
    (κ : Type v) (sets : ℕ → κ → Set (MarkedSpectralSpace Mark)) :=
  {ν : LocalWindowMeasureEncoding Mark //
    IsConsistentLocalWindowEncoding ν ∧
      HasNaturalLocalRestrictionMass sets ν}

/-- The underlying local-window encoding. -/
def LocalPointMeasureStateSpace.encoding
    {Mark : Type u} [MeasurableSpace Mark]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)}
    (ν : LocalPointMeasureStateSpace Mark κ sets) :
    LocalWindowMeasureEncoding Mark := ν.1

/-- Evaluation at one exhaustion window. -/
def LocalPointMeasureStateSpace.window
    {Mark : Type u} [MeasurableSpace Mark]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)}
    (ν : LocalPointMeasureStateSpace Mark κ sets) (n : ℕ) :
    FiniteMeasure (MarkedSpectralSpace Mark) := ν.1 n

/-- Window evaluation is continuous in the induced product weak topology. -/
theorem continuous_localPointMeasureStateSpace_window
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)} (n : ℕ) :
    Continuous (fun ν : LocalPointMeasureStateSpace Mark κ sets => ν.window n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Explicit continuity interface for all determining-family restriction
masses. -/
def LocalRestrictionMassMapsContinuous
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark)) : Prop :=
  ∀ n k, Continuous (fun ν : LocalWindowMeasureEncoding Mark =>
    ((ν n).restrict (sets n k)).mass)

/-- Under sharp-window and determining-mass continuity, the underlying locus
of the bundled state space is closed in the product weak topology. -/
theorem isClosed_localPointMeasureStateSpace_locus
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Mark))
    (hmass : LocalRestrictionMassMapsContinuous sets) :
    IsClosed {ν : LocalWindowMeasureEncoding Mark |
      IsConsistentLocalWindowEncoding ν ∧
        HasNaturalLocalRestrictionMass sets ν} := by
  apply (isClosed_isConsistentLocalWindowEncoding hsharp).inter
  change IsClosed {ν : LocalWindowMeasureEncoding Mark |
    HasNaturalLocalRestrictionMass sets ν}
  rw [show {ν : LocalWindowMeasureEncoding Mark |
      HasNaturalLocalRestrictionMass sets ν} =
      ⋂ n, ⋂ k, {ν | ((ν n).restrict (sets n k)).mass ∈
        Set.range ((↑) : ℕ → NNReal)} by
    ext ν
    simp [HasNaturalLocalRestrictionMass]]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro k
  exact isClosed_range_natCast_nnreal.preimage (hmass n k)

/-- The bundled state space is Hausdorff whenever the ambient product weak
space is Hausdorff. -/
theorem localPointMeasureStateSpace_t2
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)} :
    T2Space (LocalPointMeasureStateSpace Mark κ sets) := by
  infer_instance

/-- The induced measurable structure is Borel whenever the ambient product
measurable structure is Borel. -/
theorem localPointMeasureStateSpace_borel
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [MeasurableSpace (LocalWindowMeasureEncoding Mark)]
    [BorelSpace (LocalWindowMeasureEncoding Mark)]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)} :
    BorelSpace (LocalPointMeasureStateSpace Mark κ sets) := by
  infer_instance

/-- Compact containment pulled back to the bundled local point-measure state
space. -/
def localPointMeasureCompactContainment
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)}
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark)) :
    Set (LocalPointMeasureStateSpace Mark κ sets) :=
  Subtype.val ⁻¹' localWindowCompactContainment C K

/-- Compactness of bounded-mass, compact-support containment in the bundled
state space, conditional only on the two explicit restriction-continuity
interfaces. -/
theorem isCompact_localPointMeasureCompactContainment
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Mark))
    (hmass : LocalRestrictionMassMapsContinuous sets)
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark))
    (hK : ∀ n, IsCompact (K n)) :
    IsCompact (localPointMeasureCompactContainment (sets := sets) C K) := by
  exact (isClosed_localPointMeasureStateSpace_locus sets hsharp hmass)
    |>.isClosedEmbedding_subtypeVal
    |>.isCompact_preimage (isCompact_localWindowCompactContainment C K hK)

/-- Prokhorov subsequence theorem on the bundled state space.  The topology is
the induced product weak topology, not an asserted canonical vague topology.
All compact-containment and tail hypotheses are explicit. -/
theorem exists_weaklyConvergent_subsequence_localPointMeasureStateSpace
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    {κ : Type v} {sets : ℕ → κ → Set (MarkedSpectralSpace Mark)}
    [MeasurableSpace (LocalPointMeasureStateSpace Mark κ sets)]
    [T2Space (LocalPointMeasureStateSpace Mark κ sets)]
    [BorelSpace (LocalPointMeasureStateSpace Mark κ sets)]
    [FirstCountableTopology
      (ProbabilityMeasure (LocalPointMeasureStateSpace Mark κ sets))]
    (μs : ℕ → ProbabilityMeasure (LocalPointMeasureStateSpace Mark κ sets))
    (localCount : LocalPointMeasureStateSpace Mark κ sets → ENNReal)
    (K : ℕ → Set (LocalPointMeasureStateSpace Mark κ sets))
    (hK : ∀ m, IsCompact (K m))
    (hcontain : ∀ m, (K m)ᶜ ⊆ {x | (m : ENNReal) ≤ localCount x})
    (C : ENNReal) (hC : C ≠ ⊤)
    (htail : ∀ i m, (μs i : Measure _)
      {x | (m : ENNReal) ≤ localCount x} ≤ C / (m : ENNReal)) :
    ∃ μ : ProbabilityMeasure (LocalPointMeasureStateSpace Mark κ sets),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  exact exists_weaklyConvergent_subsequence_of_localCount_tail
    μs localCount K hK hcontain C hC htail

end CEHNative.BlockBand
