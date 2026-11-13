module
public import BlockBand.Counting.PhysicalMarkedTightnessAtoms

/-!
# Compact sets of marked configurations

The map sending a shell array to its marked point measure is continuous for the vague
topology.  Since the space of shell arrays with fixed caps is compact, its image is a
compact set of locally finite integer-valued marked configurations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
local instance : TopologicalSpace Unit := ⊥
local instance (caps : ℕ → ℕ) (j : ℕ) : TopologicalSpace (Fin (caps j) → (Unit ⊕ markedAtomShell j)) := Pi.topologicalSpace
local instance (caps : ℕ → ℕ) : TopologicalSpace (MarkedShellArray caps) := Pi.topologicalSpace
local instance : BorelSpace MarkedSpectralSpace :=
  BlockBand.Model.Construction.markedSpectralSpace_borelSpace
local instance (caps : ℕ → ℕ) : MeasurableSpace (MarkedShellIndex caps) := ⊤
local instance (caps : ℕ → ℕ) : MeasurableSingletonClass (MarkedShellIndex caps) :=
  ⟨fun _ => by trivial⟩

/-- Lift a real relatively compact set through the proper spectral projection. -/
def spectralSetMarkedLift (A : RelativelyCompactBorelSet ℝ) :
    RelativelyCompactBorelSet MarkedSpectralSpace where
  carrier := Prod.fst ⁻¹' A.carrier
  measurable := A.measurable.preimage measurable_fst
  compact_closure := by
    apply (A.compact_closure.prod (isCompact_univ : IsCompact (univ : Set MassProfile))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal
    · intro z hz
      exact ⟨subset_closure hz, mem_univ _⟩
    · exact isClosed_closure.prod isClosed_univ

/-- Build a marked point measure, with its spectral field given by the pushforward
under the proper spectral projection. -/
def properMarkedPointMeasure (ξ : VaguePointMeasure MarkedSpectralSpace) : MarkedPointMeasure where
  marked := ξ
  spectral :=
    { measure := Measure.map Prod.fst ξ.measure
      finite_on_compact := by
        intro K hK
        rw [Measure.map_apply measurable_fst hK.isClosed.measurableSet]
        apply ξ.finite_on_compact
        have heq : Prod.fst ⁻¹' K = K ×ˢ (univ : Set MassProfile) := by
          ext z
          simp
        rw [heq]
        exact hK.prod (isCompact_univ : IsCompact (univ : Set MassProfile))
      integer_valued := by
        intro A hA
        rw [Measure.map_apply measurable_fst hA]
        exact ξ.integer_valued _ (hA.preimage measurable_fst)
      count := fun A => ξ.count (spectralSetMarkedLift A)
      measure_eq_count := by
        intro A
        rw [Measure.map_apply measurable_fst A.measurable]
        exact ξ.measure_eq_count (spectralSetMarkedLift A) }
  spectral_eq := rfl

/-- The shell map from shell arrays into marked configurations. -/
def markedShellConfiguration {caps : ℕ → ℕ} (data : MarkedShellArray caps) : MarkedPointMeasure :=
  properMarkedPointMeasure (markedShellVaguePointMeasure data)

/-- The scalar test contribution of one optional atom, zero on the inactive summand. -/
def markedShellTestValue {caps : ℕ → ℕ} (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (data : MarkedShellArray caps) (i : MarkedShellIndex caps) : ℝ :=
  Sum.elim (fun _ : Unit => 0) (fun z : markedAtomShell i.1 => f z.val) (data i.1 i.2)

theorem markedShellTestValue_eq_indicator {caps : ℕ → ℕ}
    (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (data : MarkedShellArray caps) :
    (markedShellActive data).indicator (fun i => f (markedShellLocation data i)) =
      markedShellTestValue f data := by
  funext i
  cases h : data i.1 i.2 with
  | inl u => simp [markedShellActive, markedShellLocation, markedShellTestValue, h]
  | inr z =>
      have hi : i ∈ markedShellActive data := ⟨z, h⟩
      rw [Set.indicator_of_mem hi]
      simp [markedShellLocation, markedShellTestValue, h]

theorem markedShellTestValue_zero_of_lt {caps : ℕ → ℕ}
    (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (N : ℕ)
    (hN : ∀ z ∈ tsupport f, |z.1| ≤ N) (data : MarkedShellArray caps)
    (i : MarkedShellIndex caps) (hi : N < i.1) : markedShellTestValue f data i = 0 := by
  cases h : data i.1 i.2 with
  | inl u => simp [markedShellTestValue, h]
  | inr z =>
      simp only [markedShellTestValue, h, Sum.elim_inr]
      by_contra hf
      have hb := hN z.val (subset_tsupport f hf)
      have hj : (N : ℝ) < (i.1 : ℝ) := by exact_mod_cast hi
      linarith [z.2.1]

/-- Finite visible-shell formula for the integral of every compactly supported test. -/
theorem markedShellConfiguration_coordinate {caps : ℕ → ℕ}
    (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (N : ℕ)
    (hN : ∀ z ∈ tsupport f, |z.1| ≤ N) (data : MarkedShellArray caps) :
    (markedShellConfiguration data).marked.coordinate f =
      ∑ i ∈ markedShellVisibleIndices caps N, markedShellTestValue f data i := by
  classical
  simp only [markedShellConfiguration, properMarkedPointMeasure, markedShellVaguePointMeasure, VaguePointMeasure.coordinate]
  change (∫ z, f z ∂markedShellCountingMeasure data) = _
  rw [markedShellCountingMeasure, integral_map (f := fun z => f z) (measurable_of_countable _).aemeasurable
    (show AEStronglyMeasurable (fun z => f z) _ from f.continuous.aestronglyMeasurable)]
  rw [← integral_indicator (Set.to_countable (markedShellActive data)).measurableSet,
    markedShellTestValue_eq_indicator]
  have hz : ∀ i, i ∉ (markedShellVisibleIndices caps N : Set (MarkedShellIndex caps)) →
      markedShellTestValue f data i = 0 := by
    intro i hi
    apply markedShellTestValue_zero_of_lt f N hN data i
    exact lt_of_not_ge (fun hle => hi ((mem_markedShellVisibleIndices caps N i).mpr hle))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hin : IntegrableOn (markedShellTestValue f data)
      (markedShellVisibleIndices caps N : Set (MarkedShellIndex caps)) Measure.count := by
    rw [← (markedShellVisibleIndices caps N : Set (MarkedShellIndex caps)).biUnion_of_singleton]
    simp [integrableOn_finset_iUnion, integrableOn_singleton_iff]
  rw [setIntegral_finset _ hin]
  simp only [count_real_singleton, one_smul]

theorem continuous_markedShellTestValue {caps : ℕ → ℕ}
    (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (i : MarkedShellIndex caps) :
    Continuous (fun data : MarkedShellArray caps => markedShellTestValue f data i) := by
  have hs : Continuous (Sum.elim (fun _ : Unit => (0 : ℝ))
      (fun z : markedAtomShell i.1 => f z.val)) :=
    continuous_sum_dom.mpr ⟨continuous_const, f.continuous.comp continuous_subtype_val⟩
  exact hs.comp ((continuous_apply i.2).comp (continuous_apply i.1))

/-- The shell map is continuous for the vague topology. -/
theorem continuous_markedShellConfiguration (caps : ℕ → ℕ) :
    Continuous (markedShellConfiguration (caps := caps)) := by
  rw [continuous_induced_rng]
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  obtain ⟨N, hN⟩ := exists_nat_bound_markedCompact (tsupport f) f.hasCompactSupport
  change Continuous (fun data : MarkedShellArray caps => (markedShellConfiguration data).marked.coordinate f)
  simp_rw [markedShellConfiguration_coordinate f N hN]
  exact continuous_finsetSum _ fun i _ => continuous_markedShellTestValue f i

/-- The image of the shell map: a vaguely compact set of locally finite integer marked
configurations. -/
def markedShellCompactSet (caps : ℕ → ℕ) : Set MarkedPointMeasure :=
  Set.range (markedShellConfiguration (caps := caps))

theorem isCompact_markedShellCompactSet (caps : ℕ → ℕ) : IsCompact (markedShellCompactSet caps) :=
  isCompact_range (continuous_markedShellConfiguration caps)

end BlockBand.Counting
