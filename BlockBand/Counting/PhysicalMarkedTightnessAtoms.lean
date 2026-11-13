module
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences
public import BlockBand.Counting.SimpleSpectralLimitsTopology
public import Mathlib.Topology.Constructions
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Shell arrays of marked atoms

The marked spectral space is cut into compact shells `|x| ∈ [j, j+1]`.  Given caps
`caps j`, a shell array assigns to each of the `caps j` cells of shell `j` either nothing
or an atom of that shell.  Each array defines a locally finite integer-valued marked point
measure; this is the parametrization used for compact sets of marked configurations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
local instance : BorelSpace MarkedSpectralSpace :=
  BlockBand.Model.Construction.markedSpectralSpace_borelSpace

/-- The closed shell `j` of the marked spectral space. -/
def markedAtomShell (j : ℕ) : Set MarkedSpectralSpace :=
  {z | (j : ℝ) ≤ |z.1| ∧ |z.1| ≤ (j : ℝ) + 1}

theorem isCompact_markedAtomShell (j : ℕ) : IsCompact (markedAtomShell j) := by
  apply (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set MassProfile))).of_isClosed_subset
    ((isClosed_le continuous_const continuous_fst.abs).inter
      (isClosed_le continuous_fst.abs continuous_const))
  rintro z ⟨hlo, hhi⟩
  exact ⟨abs_le.mp hhi, mem_univ _⟩

theorem markedAtomShell_compactSpace (j : ℕ) : CompactSpace (markedAtomShell j) :=
  isCompact_iff_compactSpace.mp (isCompact_markedAtomShell j)
attribute [instance] markedAtomShell_compactSpace

abbrev MarkedShellIndex (caps : ℕ → ℕ) := Σ j : ℕ, Fin (caps j)
local instance : TopologicalSpace Unit := ⊥
abbrev MarkedShellArray (caps : ℕ → ℕ) := ∀ j : ℕ, Fin (caps j) → (Unit ⊕ (markedAtomShell j))
local instance (caps : ℕ → ℕ) (j : ℕ) : TopologicalSpace (Fin (caps j) → (Unit ⊕ markedAtomShell j)) := Pi.topologicalSpace
local instance (caps : ℕ → ℕ) : TopologicalSpace (MarkedShellArray caps) := Pi.topologicalSpace
local instance (caps : ℕ → ℕ) : MeasurableSpace (MarkedShellIndex caps) := ⊤
local instance (caps : ℕ → ℕ) : MeasurableSingletonClass (MarkedShellIndex caps) :=
  ⟨fun _ => by trivial⟩

theorem markedShellArray_compactSpace (caps : ℕ → ℕ) : CompactSpace (MarkedShellArray caps) := by
  infer_instance
attribute [instance] markedShellArray_compactSpace

/-- A default marked atom, used only on inactive indices. -/
def inactiveMarkedAtom : MarkedSpectralSpace :=
  (0, ⟨Measure.dirac (0 : Torus), inferInstance⟩)

def markedShellActive {caps : ℕ → ℕ} (data : MarkedShellArray caps) : Set (MarkedShellIndex caps) :=
  {i | ∃ z, data i.1 i.2 = Sum.inr z}

def markedShellLocation {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (i : MarkedShellIndex caps) : MarkedSpectralSpace :=
  Sum.elim (fun _ : Unit => inactiveMarkedAtom) Subtype.val (data i.1 i.2)

theorem markedShellLocation_lower {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (i : MarkedShellIndex caps) (hi : i ∈ markedShellActive data) :
    (i.1 : ℝ) ≤ |(markedShellLocation data i).1| := by
  cases h : data i.1 i.2 with
  | inl u => simp [markedShellActive, h] at hi
  | inr z => simpa [markedShellLocation, h] using z.2.1

/-- A finite set containing every cell in the first `N + 1` shells. -/
def markedShellVisibleIndices (caps : ℕ → ℕ) (N : ℕ) : Finset (MarkedShellIndex caps) :=
  (Finset.range (N+1)).sigma fun _ => Finset.univ

theorem mem_markedShellVisibleIndices (caps : ℕ → ℕ) (N : ℕ) (i : MarkedShellIndex caps) :
    i ∈ markedShellVisibleIndices caps N ↔ i.1 ≤ N := by
  simp [markedShellVisibleIndices]

/-- Compact marked sets see only finitely many shells. -/
theorem exists_nat_bound_markedCompact (K : Set MarkedSpectralSpace) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ z ∈ K, |z.1| ≤ N := by
  obtain ⟨R, hR⟩ := (hK.image continuous_fst.abs).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, hz, rfl⟩).trans hN⟩

theorem markedShell_active_preimage_finite {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (K : Set MarkedSpectralSpace) (hK : IsCompact K) :
    ((markedShellLocation data ⁻¹' K) ∩ markedShellActive data).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_bound_markedCompact K hK
  apply (markedShellVisibleIndices caps N).finite_toSet.subset
  rintro i ⟨hiK, hiA⟩
  apply (mem_markedShellVisibleIndices caps N i).mpr
  exact_mod_cast (markedShellLocation_lower data i hiA).trans (hN _ hiK)

/-- Marked counting measure: the map of counting measure restricted to active cells. -/
def markedShellCountingMeasure {caps : ℕ → ℕ} (data : MarkedShellArray caps) : Measure MarkedSpectralSpace :=
  Measure.map (markedShellLocation data) (Measure.count.restrict (markedShellActive data))

theorem markedShellCountingMeasure_apply {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (A : Set MarkedSpectralSpace) (hA : MeasurableSet A) :
    markedShellCountingMeasure data A =
      Measure.count ((markedShellLocation data ⁻¹' A) ∩ markedShellActive data) := by
  rw [markedShellCountingMeasure, Measure.map_apply (measurable_of_countable _) hA,
    Measure.restrict_apply (hA.preimage (measurable_of_countable (markedShellLocation data)))]

theorem markedShellCountingMeasure_finite_on_compact {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (K : Set MarkedSpectralSpace) (hK : IsCompact K) : markedShellCountingMeasure data K < ∞ := by
  rw [markedShellCountingMeasure_apply data K hK.isClosed.measurableSet]
  exact Measure.count_apply_lt_top.mpr (markedShell_active_preimage_finite data K hK)

theorem markedShellCountingMeasure_integer {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (A : Set MarkedSpectralSpace) (hA : MeasurableSet A) :
    markedShellCountingMeasure data A = ∞ ∨ ∃ n : ℕ, markedShellCountingMeasure data A = (n : ℝ≥0∞) := by
  rw [markedShellCountingMeasure_apply data A hA]
  by_cases hf : ((markedShellLocation data ⁻¹' A) ∩ markedShellActive data).Finite
  · exact Or.inr ⟨hf.toFinset.card, Measure.count_apply_finite _ hf⟩
  · exact Or.inl (Measure.count_apply_infinite hf)

/-- Only finitely many active cells lie in any relatively compact Borel set. -/
theorem markedShellCarrierIndices_finite {caps : ℕ → ℕ} (data : MarkedShellArray caps)
    (A : RelativelyCompactBorelSet MarkedSpectralSpace) :
    ((markedShellLocation data ⁻¹' A.carrier) ∩ markedShellActive data).Finite :=
  (markedShell_active_preimage_finite data (closure A.carrier) A.compact_closure).subset
    (by intro i hi; exact ⟨subset_closure hi.1, hi.2⟩)

/-- The locally finite integer-valued marked point measure of a shell array. -/
def markedShellVaguePointMeasure {caps : ℕ → ℕ} (data : MarkedShellArray caps) :
    VaguePointMeasure MarkedSpectralSpace where
  measure := markedShellCountingMeasure data
  finite_on_compact := markedShellCountingMeasure_finite_on_compact data
  integer_valued := markedShellCountingMeasure_integer data
  count := fun A => (markedShellCarrierIndices_finite data A).toFinset.card
  measure_eq_count := by
    intro A
    rw [markedShellCountingMeasure_apply data A.carrier A.measurable]
    exact Measure.count_apply_finite _ (markedShellCarrierIndices_finite data A)

end BlockBand.Counting
