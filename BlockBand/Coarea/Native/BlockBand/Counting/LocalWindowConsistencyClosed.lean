module

public import BlockBand.Coarea.Native.BlockBand.Counting.LocallyFiniteConfiguration
public import Mathlib.Topology.Instances.Nat

/-!
# Closure properties for the local-window configuration encoding

This module studies the projective encoding introduced in
`LocallyFiniteConfiguration`.  Sharp restriction of a weakly convergent
measure is not continuous when the limiting measure charges the boundary of
the restricting window.  We therefore state and prove the exact closure
principle under convergence of the relevant restrictions.  This is the
natural boundary-null continuity input needed for the usual vague-topology
argument; Mathlib currently provides its Portmanteau null-frontier theorem for
probability measures, but not the corresponding bundled restriction theorem
for arbitrary finite measures.

We also construct the subtype of projectively consistent encodings, prove its
Hausdorff property, and prove an unconditional closedness result for the
necessary integer-valued condition that every window has natural-number total
mass.  The latter is weaker than saying that the measure of every Borel set is
integer-valued, so no unjustified point-measure closure or counting theorem is
claimed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal

universe u v

/-- The common state space cut down to projectively consistent sharp-window
restrictions. -/
abbrev ConsistentLocalWindowConfiguration
    (Mark : Type u) [MeasurableSpace Mark] :=
  {ν : LocalWindowMeasureEncoding Mark // IsConsistentLocalWindowEncoding ν}

/-- Evaluation of a consistent encoding at a fixed window. -/
def ConsistentLocalWindowConfiguration.window
    {Mark : Type u} [MeasurableSpace Mark]
    (ν : ConsistentLocalWindowConfiguration Mark) (n : ℕ) :
    FiniteMeasure (MarkedSpectralSpace Mark) :=
  ν.1 n

/-- Window evaluation is continuous in the inherited product topology. -/
theorem continuous_consistentLocalWindowConfiguration_window
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)] (n : ℕ) :
    Continuous (fun ν : ConsistentLocalWindowConfiguration Mark => ν.window n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- The consistent subtype is Hausdorff under the same exact hypotheses as
the ambient weak finite-measure product. -/
theorem consistentLocalWindowConfiguration_t2
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [HasOuterApproxClosed (MarkedSpectralSpace Mark)] :
    T2Space (ConsistentLocalWindowConfiguration Mark) := by
  infer_instance

/-- Projective consistency passes to a coordinatewise weak limit whenever
sharp restriction to each smaller window also converges.  Boundary-null
Portmanteau arguments are precisely what supplies `hrestrict` in the classical
vague-topology construction. -/
theorem isConsistentLocalWindowEncoding_of_tendsto
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} {L : Filter κ} [NeBot L]
    {νs : κ → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hνs : ∀ q, IsConsistentLocalWindowEncoding (νs q))
    (hν : Tendsto νs L (𝓝 ν))
    (hrestrict : ∀ m n, m ≤ n →
      Tendsto (fun q => (νs q n).restrict (markedSpectralWindow Mark m)) L
        (𝓝 ((ν n).restrict (markedSpectralWindow Mark m)))) :
    IsConsistentLocalWindowEncoding ν := by
  intro m n hmn
  have hm : Tendsto (fun q => νs q m) L (𝓝 (ν m)) :=
    ((continuous_apply m).tendsto ν).comp hν
  have heq : (fun q => (νs q n).restrict (markedSpectralWindow Mark m)) =
      fun q => νs q m := by
    funext q
    exact hνs q m n hmn
  exact tendsto_nhds_unique (hrestrict m n hmn) (by simpa [heq] using hm)

/-- Global continuity of every sharp-window restriction map.  This strong
property is false without excluding boundary-charging measures, but it is a
useful exact interface for a boundary-regular subspace. -/
def SharpWindowRestrictionMapsContinuous
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)] : Prop :=
  ∀ m, Continuous (fun μ : FiniteMeasure (MarkedSpectralSpace Mark) =>
    μ.restrict (markedSpectralWindow Mark m))

/-- Under continuity of sharp restriction, the projective consistency locus
is closed: it is a countable intersection of equalizers of continuous maps. -/
theorem isClosed_isConsistentLocalWindowEncoding
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Mark)) :
    IsClosed {ν : LocalWindowMeasureEncoding Mark |
      IsConsistentLocalWindowEncoding ν} := by
  rw [show {ν : LocalWindowMeasureEncoding Mark |
      IsConsistentLocalWindowEncoding ν} =
      ⋂ m, ⋂ n, if h : m ≤ n then
        {ν | (ν n).restrict (markedSpectralWindow Mark m) = ν m}
      else Set.univ by
    ext ν
    constructor
    · intro h
      simp only [Set.mem_iInter]
      intro m n
      split_ifs with hmn
      · exact h m n hmn
      · exact Set.mem_univ ν
    · intro h m n hmn
      have hm := Set.mem_iInter.mp h m
      have hn := Set.mem_iInter.mp hm n
      simpa [hmn] using hn]
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro n
  split_ifs with hmn
  · exact isClosed_eq
      ((hsharp m).comp (continuous_apply n)) (continuous_apply m)
  · exact isClosed_univ

/-- Null mass on all sharp window boundaries, the standard sufficient
hypothesis for continuity of restriction under weak convergence. -/
def HasNullMarkedWindowBoundaries
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ n m, (ν n : Measure (MarkedSpectralSpace Mark))
    (frontier (markedSpectralWindow Mark m)) = 0

/-- An explicit interface for the one missing finite-measure Portmanteau
corollary: weak convergence to a boundary-null coordinate implies convergence
of every sharp restriction.  Keeping this as a proposition on a particular
net avoids postulating any global axiom. -/
def SharpWindowRestrictionsConverge
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    {κ : Type v} (L : Filter κ)
    (νs : κ → LocalWindowMeasureEncoding Mark)
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ m n, m ≤ n →
    Tendsto (fun q => (νs q n).restrict (markedSpectralWindow Mark m)) L
      (𝓝 ((ν n).restrict (markedSpectralWindow Mark m)))

/-- Boundary-regular consistency closure, conditional only on the sharply
identified restriction-convergence corollary. -/
theorem isConsistent_of_nullBoundaries_of_sharpRestrictionsConverge
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} {L : Filter κ} [NeBot L]
    {νs : κ → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hνs : ∀ q, IsConsistentLocalWindowEncoding (νs q))
    (hν : Tendsto νs L (𝓝 ν))
    (_hboundary : HasNullMarkedWindowBoundaries ν)
    (hsharp : SharpWindowRestrictionsConverge L νs ν) :
    IsConsistentLocalWindowEncoding ν :=
  isConsistentLocalWindowEncoding_of_tendsto hνs hν (by exact hsharp)

/-- A necessary integer-valuedness condition for a point configuration: every
window coordinate has natural-number total mass. -/
def HasNaturalLocalWindowMass
    {Mark : Type u} [MeasurableSpace Mark]
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ n, (ν n).mass ∈ Set.range ((↑) : ℕ → NNReal)

/-- Natural numbers form a closed subset of the nonnegative reals. -/
theorem isClosed_range_natCast_nnreal :
    IsClosed (Set.range ((↑) : ℕ → NNReal)) := by
  have hpre : Set.range ((↑) : ℕ → NNReal) =
      NNReal.toReal ⁻¹' Set.range ((↑) : ℕ → ℝ) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply NNReal.eq
      simpa using hn
  rw [hpre]
  exact Nat.isClosedEmbedding_coe_real.isClosed_range.preimage continuous_subtype_val

/-- The natural-local-mass locus is closed in the product weak topology.  This
is an unconditional integer-valued closure statement available from the
continuity of finite-measure total mass. -/
theorem isClosed_hasNaturalLocalWindowMass
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)] :
    IsClosed {ν : LocalWindowMeasureEncoding Mark |
      HasNaturalLocalWindowMass ν} := by
  rw [show {ν : LocalWindowMeasureEncoding Mark |
      HasNaturalLocalWindowMass ν} =
      ⋂ n, {ν : LocalWindowMeasureEncoding Mark |
        (ν n).mass ∈ Set.range ((↑) : ℕ → NNReal)} by
    ext ν
    simp [HasNaturalLocalWindowMass]]
  apply isClosed_iInter
  intro n
  exact isClosed_range_natCast_nnreal.preimage
    (FiniteMeasure.continuous_mass.comp (continuous_apply n))

/-- Intersecting compact local-window containment with the closed
natural-mass condition remains compact. -/
theorem isCompact_localWindowCompactContainment_naturalMass
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark))
    (hK : ∀ n, IsCompact (K n)) :
    IsCompact (localWindowCompactContainment C K ∩
      {ν | HasNaturalLocalWindowMass ν}) :=
  (isCompact_localWindowCompactContainment C K hK).inter_right
    isClosed_hasNaturalLocalWindowMass

/-- Compact containment with natural local masses, pulled back to the
consistent configuration subtype. -/
def consistentLocalWindowCompactContainmentNaturalMass
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark)) :
    Set (ConsistentLocalWindowConfiguration Mark) :=
  Subtype.val ⁻¹' (localWindowCompactContainment C K ∩
    {ν | HasNaturalLocalWindowMass ν})

/-- If sharp restriction is continuous on the chosen ambient subspace, the
consistent compact-containment set is compact. -/
theorem isCompact_consistentLocalWindowCompactContainmentNaturalMass
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [T2Space Mark] [BorelSpace Mark]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Mark))
    (C : ℕ → NNReal) (K : ℕ → Set (MarkedSpectralSpace Mark))
    (hK : ∀ n, IsCompact (K n)) :
    IsCompact (consistentLocalWindowCompactContainmentNaturalMass C K) := by
  exact (isClosed_isConsistentLocalWindowEncoding hsharp).isClosedEmbedding_subtypeVal
    |>.isCompact_preimage
      (isCompact_localWindowCompactContainment_naturalMass C K hK)

/-- The consistent subtype inherits the Borel structure whenever the common
ambient product has its Borel measurable structure.  Establishing that
ambient instance from Mathlib's current finite-measure API remains an explicit
hypothesis rather than being silently postulated. -/
theorem consistentLocalWindowConfiguration_borel
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [MeasurableSpace (LocalWindowMeasureEncoding Mark)]
    [BorelSpace (LocalWindowMeasureEncoding Mark)] :
    BorelSpace (ConsistentLocalWindowConfiguration Mark) := by
  infer_instance

end CoareaNative.BlockBand
