module

public import BlockBand.Coarea.Native.BlockBand.Counting.LocalWindowConsistencyClosed

/-!
# Integer-valued local restrictions under coordinatewise weak limits

This module records the next closure step for the common local-window
encoding.  Integer-valuedness is tested on an explicit countable family of
local restrictions.  The exact boundary-null Portmanteau input is represented
by convergence of the corresponding restricted masses; no full vague topology
or bundled point-measure space is asserted.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal

universe u v w

/-- Every restriction in a chosen countable local determining family has
natural-number mass.  Using bundled `FiniteMeasure.mass : NNReal` avoids the
spurious `∞` limit available in `ENNReal`. -/
def HasNaturalLocalRestrictionMass
    {Mark : Type u} [MeasurableSpace Mark]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ n k, ((ν n).restrict (sets n k)).mass ∈
    Set.range ((↑) : ℕ → NNReal)

/-- Boundary-nullness for every member of a local determining family.  This is
the standard hypothesis under which Portmanteau yields convergence of the
restricted masses. -/
def HasNullLocalRestrictionBoundaries
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ n k, (ν n : Measure (MarkedSpectralSpace Mark)) (frontier (sets n k)) = 0

/-- Exact finite-measure Portmanteau interface required by integer closure:
all restricted total masses converge in `NNReal`. -/
def LocalRestrictionMassesConverge
    {Mark : Type u} [MeasurableSpace Mark]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} (L : Filter α)
    (νs : α → LocalWindowMeasureEncoding Mark)
    (ν : LocalWindowMeasureEncoding Mark) : Prop :=
  ∀ n k, Tendsto
    (fun q => ((νs q n).restrict (sets n k)).mass) L
    (𝓝 (((ν n).restrict (sets n k)).mass))

/-- Natural-valued local restriction masses are closed under a limit whenever
the corresponding masses converge. -/
theorem hasNaturalLocalRestrictionMass_of_tendsto
    {Mark : Type u} [MeasurableSpace Mark]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {L : Filter α} [NeBot L]
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hnat : ∀ q, HasNaturalLocalRestrictionMass sets (νs q))
    (hmass : LocalRestrictionMassesConverge sets L νs ν) :
    HasNaturalLocalRestrictionMass sets ν := by
  intro n k
  exact isClosed_range_natCast_nnreal.mem_of_tendsto
    (hmass n k) (Eventually.of_forall fun q => hnat q n k)

/-- Boundary-null formulation of restriction-mass closure.  The boundary
hypothesis documents why the explicit Portmanteau interface `hmass` is valid;
Mathlib does not currently bundle that corollary for arbitrary finite
measures. -/
theorem hasNaturalLocalRestrictionMass_of_nullBoundaries
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {L : Filter α} [NeBot L]
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (hnat : ∀ q, HasNaturalLocalRestrictionMass sets (νs q))
    (_hboundary : HasNullLocalRestrictionBoundaries sets ν)
    (hmass : LocalRestrictionMassesConverge sets L νs ν) :
    HasNaturalLocalRestrictionMass sets ν :=
  hasNaturalLocalRestrictionMass_of_tendsto sets hnat hmass

/-- Combined closure input for an exhaustion limit.  It separates the two
continuity statements that a vague-topology construction would
supply: convergence of sharp window restrictions and convergence of the
chosen local restriction masses. -/
structure IntegerPointMeasureClosureInput
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} (L : Filter α)
    (νs : α → LocalWindowMeasureEncoding Mark)
    (ν : LocalWindowMeasureEncoding Mark) : Prop where
  approximants_consistent : ∀ q, IsConsistentLocalWindowEncoding (νs q)
  approximants_integer : ∀ q, HasNaturalLocalRestrictionMass sets (νs q)
  encoding_tendsto : Tendsto νs L (𝓝 ν)
  limit_boundary_null : HasNullMarkedWindowBoundaries ν
  sharp_restrictions_converge : SharpWindowRestrictionsConverge L νs ν
  determining_boundaries_null : HasNullLocalRestrictionBoundaries sets ν
  restriction_masses_converge : LocalRestrictionMassesConverge sets L νs ν

/-- Compatibility across the exhaustion and integer-valuedness on the chosen
local determining family pass simultaneously to the limit. -/
theorem consistent_and_integer_of_closureInput
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    [OpensMeasurableSpace (MarkedSpectralSpace Mark)]
    [T2Space (FiniteMeasure (MarkedSpectralSpace Mark))]
    {κ : Type v} (sets : ℕ → κ → Set (MarkedSpectralSpace Mark))
    {α : Type w} {L : Filter α} [NeBot L]
    {νs : α → LocalWindowMeasureEncoding Mark}
    {ν : LocalWindowMeasureEncoding Mark}
    (input : IntegerPointMeasureClosureInput sets L νs ν) :
    IsConsistentLocalWindowEncoding ν ∧
      HasNaturalLocalRestrictionMass sets ν := by
  constructor
  · exact isConsistent_of_nullBoundaries_of_sharpRestrictionsConverge
      input.approximants_consistent input.encoding_tendsto
      input.limit_boundary_null input.sharp_restrictions_converge
  · exact hasNaturalLocalRestrictionMass_of_nullBoundaries sets
      input.approximants_integer input.determining_boundaries_null
      input.restriction_masses_converge

/-- Projective compatibility explicitly identifies every smaller exhaustion
coordinate with the restriction of a larger coordinate. -/
theorem restriction_eq_of_consistent_integerClosure
    {Mark : Type u} [MeasurableSpace Mark]
    {ν : LocalWindowMeasureEncoding Mark}
    (_hnat : HasNaturalLocalRestrictionMass
      (fun n (_ : Unit) => markedSpectralWindow Mark n) ν)
    (hν : IsConsistentLocalWindowEncoding ν)
    {m n : ℕ} (hmn : m ≤ n) :
    (ν n).restrict (markedSpectralWindow Mark m) = ν m :=
  hν m n hmn

/-- Compact-containment interface for the candidate limit.  This packages
exactly the deterministic local mass/support conclusion inherited from the
compact product set, without identifying the ambient topology with a vague
point-measure topology. -/
theorem local_mass_support_of_compactContainment_integerClosure
    {Mark : Type u} [MeasurableSpace Mark] [TopologicalSpace Mark]
    {C : ℕ → NNReal} {K : ℕ → Set (MarkedSpectralSpace Mark)}
    {ν : LocalWindowMeasureEncoding Mark}
    (hν : ν ∈ localWindowCompactContainment C K) :
    ∀ n, (ν n).mass ≤ C n ∧ ν n (K n)ᶜ = 0 :=
  (mem_localWindowCompactContainment_iff ν).mp hν

end CoareaNative.BlockBand
