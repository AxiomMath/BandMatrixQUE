module

public import BlockBand.Coarea.Native.BlockBand.Counting.PSSSRationalWindowTightness
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A weak product topology for rational-window limits

Sharp restriction to a closed interval is not continuous on the full space of
finite measures: atoms may cross the boundary.  This module therefore performs
the compactness argument in the ambient countable product of finite-measure
spaces, each with Mathlib's weak topology.  The finite BlockGUE configurations
land in this space through their local counting measures.  Coordinate
mass is continuous, coordinate support is compact, and the PSSS tails hence
produce tightness and a weakly convergent subsequence without any global sharp
restriction continuity assumption.

Counts on a particular rational interval are to be read only at limits which
charge no boundary.  The final declarations isolate this local Portmanteau condition.  The ambient product limit is not asserted here to be an integer-valued,
projectively consistent point measure, since that closure statement requires a
separate vague-topology reconstruction argument.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u

/-- The ambient rational-window state: a countable product of finite
measures with the coordinatewise weak topology. -/
abbrev VagueRationalWindowState := LocalWindowMeasureEncoding Unit

/-- Forget the conditional bundled point-state structure and retain its ambient weak-product coordinates. -/
def RationalWindowPointState.toVagueState
    (ν : RationalWindowPointState) : VagueRationalWindowState := ν.1

/-- The forgetful map into the ambient weak-product state is continuous. -/
theorem continuous_toVagueState :
    Continuous (RationalWindowPointState.toVagueState) :=
  continuous_subtype_val

/-- The finite unfolded BlockGUE configuration in the ambient weak
product. -/
def BlockGUE.unfoldedVagueRationalWindowState
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω) : VagueRationalWindowState :=
  (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ ω).1

/-- The ambient law is the pushforward of the already measurable finite state
law by the continuous forgetful map. -/
def PSSSRationalWindowSequence.vagueLaw
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i : ℕ) : ProbabilityMeasure VagueRationalWindowState :=
  (seq.law i).map RationalWindowPointState.toVagueState

/-- Coordinate mass superlevel events are Borel in the ambient product weak
topology. -/
theorem measurableSet_vagueRationalWindowState_mass_gt
    [OpensMeasurableSpace VagueRationalWindowState]
    (a : NNReal) (n : ℕ) :
    MeasurableSet {ν : VagueRationalWindowState | a < (ν n).mass} := by
  exact (isOpen_lt continuous_const
    (FiniteMeasure.continuous_mass.comp
      (continuous_localWindowMeasureEvaluation n))).measurableSet

/-- The ambient diagonal compact set uses only coordinatewise weak compactness:
mass is capped and the `n`th measure is supported in `[-n,n] × Unit`. -/
def vagueRationalWindowCompactSet (C : ℕ → NNReal) :
    Set VagueRationalWindowState :=
  localWindowCompactContainment C (markedSpectralWindow Unit)

/-- Ambient diagonal containment is compact unconditionally. -/
theorem isCompact_vagueRationalWindowCompactSet (C : ℕ → NNReal) :
    IsCompact (vagueRationalWindowCompactSet C) := by
  apply isCompact_localWindowCompactContainment
  intro n
  exact isCompact_markedSpectralWindow_inter_marks n isCompact_univ

/-- On finite point states, failure of ambient compact containment can
only come from a coordinate mass cap; compact support is automatic. -/
theorem preimage_compl_vagueRationalWindowCompactSet_subset_iUnion_massTail
    (C : ℕ → NNReal) :
    RationalWindowPointState.toVagueState ⁻¹'
        (vagueRationalWindowCompactSet C)ᶜ ⊆
      ⋃ n, {ν : RationalWindowPointState |
        (C n : ENNReal) < ((ν.window n).mass : ENNReal)} := by
  intro ν hν
  apply compl_rationalWindowPointCompactSet_subset_iUnion_massTail C
  exact hν

/-- The ambient pushforward law obeys the same PSSS coordinate tail as the
finite bundled law. -/
theorem PSSSRationalWindowSequence.vague_mass_tail
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i m n : ℕ) :
    (seq.vagueLaw i : Measure _)
        {ν : VagueRationalWindowState |
          (psssRationalWindowMassCap seq m n : ENNReal) <
            ((ν n).mass : ENNReal)} ≤
      psssRationalWindowTailSchedule m n := by
  let E : Set VagueRationalWindowState :=
    {ν | (psssRationalWindowMassCap seq m n : ENNReal) <
      ((ν n).mass : ENNReal)}
  have hE : MeasurableSet E := by
    unfold E
    convert measurableSet_vagueRationalWindowState_mass_gt
      (psssRationalWindowMassCap seq m n) n using 1
    ext ν
    exact_mod_cast Iff.rfl
  change (Measure.map RationalWindowPointState.toVagueState
    (seq.law i : Measure _)) E ≤ _
  rw [Measure.map_apply continuous_toVagueState.measurable hE]
  simpa [E, RationalWindowPointState.toVagueState,
    LocalPointMeasureStateSpace.window] using seq.mass_tail i m n

/-- PSSS summable tails bound the complement of the ambient compact
containment set. -/
theorem PSSSRationalWindowSequence.measure_compl_vagueCompactSet_le
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i m : ℕ) :
    (seq.vagueLaw i : Measure _)
        (vagueRationalWindowCompactSet
          (psssRationalWindowMassCap seq m))ᶜ ≤
      ∑' n, psssRationalWindowTailSchedule m n := by
  let K := vagueRationalWindowCompactSet (psssRationalWindowMassCap seq m)
  have hK : MeasurableSet K :=
    (isCompact_vagueRationalWindowCompactSet
      (psssRationalWindowMassCap seq m)).measurableSet
  change (Measure.map RationalWindowPointState.toVagueState
    (seq.law i : Measure _)) Kᶜ ≤ _
  rw [Measure.map_apply continuous_toVagueState.measurable hK.compl]
  calc
    (seq.law i : Measure _) (RationalWindowPointState.toVagueState ⁻¹' Kᶜ) ≤
        (seq.law i : Measure _) (⋃ n,
          {ν : RationalWindowPointState |
            (psssRationalWindowMassCap seq m n : ENNReal) <
              ((ν.window n).mass : ENNReal)}) :=
      measure_mono
        (preimage_compl_vagueRationalWindowCompactSet_subset_iUnion_massTail
          (psssRationalWindowMassCap seq m))
    _ ≤ ∑' n, (seq.law i : Measure _)
          {ν : RationalWindowPointState |
            (psssRationalWindowMassCap seq m n : ENNReal) <
              ((ν.window n).mass : ENNReal)} := measure_iUnion_le _
    _ ≤ ∑' n, psssRationalWindowTailSchedule m n :=
      ENNReal.tsum_le_tsum fun n => seq.mass_tail i m n

/-- The ambient unfolded laws are tight with no sharp-window
continuity assumptions. -/
theorem PSSSRationalWindowSequence.isTight_vagueLaw
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input) :
    IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ seq.vagueLaw)) := by
  apply isTightMeasureSet_range_of_compact_exhaustion seq.vagueLaw
    (fun m => vagueRationalWindowCompactSet
      (psssRationalWindowMassCap seq m))
    (fun m => isCompact_vagueRationalWindowCompactSet _)
    (fun m => ∑' n, psssRationalWindowTailSchedule m n)
    tendsto_tsum_psssRationalWindowTailSchedule
  intro i m
  exact seq.measure_compl_vagueCompactSet_le i m

/-- Prokhorov gives a weakly convergent subsequence in the
ambient weak-product topology, using only the external PSSS count estimate. -/
theorem PSSSRationalWindowSequence.exists_vague_weak_subsequence
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input) :
    ∃ μ : ProbabilityMeasure VagueRationalWindowState,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_of_isTight seq.vagueLaw
  exact seq.isTight_vagueLaw

/-- Weak convergence in the ambient product implies weak convergence of every
finite-measure coordinate. -/
theorem tendsto_vagueRationalWindowState_coordinate
    {ι : Type*} {l : Filter ι}
    {νs : ι → VagueRationalWindowState} {ν : VagueRationalWindowState}
    (hν : Tendsto νs l (𝓝 ν)) (n : ℕ) :
    Tendsto (fun i => νs i n) l (𝓝 (ν n)) :=
  ((continuous_localWindowMeasureEvaluation n).tendsto ν).comp hν

/-- Finite-measure Portmanteau at a nonzero boundary-null limit.  Mathlib's
Portmanteau theorem is stated for probability measures; normalization and
convergence of total masses give the finite-measure version needed for local
point-count coordinates. -/
theorem FiniteMeasure.tendsto_apply_of_null_frontier_of_tendsto
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {l : Filter ι} {νs : ι → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) (hν0 : ν ≠ 0) {E : Set Ω}
    (hboundary : ν (frontier E) = 0) :
    Tendsto (fun i => νs i E) l (𝓝 (ν E)) := by
  have hnorm : Tendsto (fun i => (νs i).normalize) l (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hν hν0
  have hboundary' : ν.normalize (frontier E) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν0, hboundary, mul_zero]
  have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hnorm hboundary'
  have hmul := hν.mass.mul hset
  simpa only [FiniteMeasure.self_eq_mass_mul_normalize] using hmul

/-- The zero-limit case is automatic from convergence of total mass, so the
finite-measure Portmanteau statement holds without a nonzero hypothesis. -/
theorem FiniteMeasure.tendsto_apply_of_null_frontier
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {l : Filter ι} {νs : ι → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νs l (𝓝 ν)) {E : Set Ω}
    (hboundary : ν (frontier E) = 0) :
    Tendsto (fun i => νs i E) l (𝓝 (ν E)) := by
  by_cases hν0 : ν = 0
  · subst ν
    simp only [FiniteMeasure.coeFn_zero, Pi.zero_apply]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hν.mass
    · exact fun i => bot_le
    · intro i
      apply ENNReal.coe_le_coe.mp
      simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        FiniteMeasure.ennreal_mass] using
        (measure_mono (μ := (νs i : Measure Ω)) (Set.subset_univ E))
  · exact FiniteMeasure.tendsto_apply_of_null_frontier_of_tendsto
      hν hν0 hboundary

/-- Therefore weak convergence of one ambient coordinate transfers every
rational-window count whose boundary is null for the limit measure. -/
theorem tendsto_rationalWindow_count_of_tendsto
    {ι : Type*} {l : Filter ι}
    {νs : ι → FiniteMeasure (MarkedSpectralSpace Unit)}
    {ν : FiniteMeasure (MarkedSpectralSpace Unit)}
    (hν : Tendsto νs l (𝓝 ν))
    (n : ℕ) (q : ℚ × ℚ)
    (hboundary : ν (frontier
      (rationalWindowDeterminingFamily n q)) = 0) :
    Tendsto (fun i => νs i (rationalWindowDeterminingFamily n q)) l
      (𝓝 (ν (rationalWindowDeterminingFamily n q))) :=
  FiniteMeasure.tendsto_apply_of_null_frontier
    hν hboundary

/-- Local Portmanteau transfer for a rational interval.  The assumptions concern only this
one approximating family, this one interval, and this one limit coordinate.
They are exactly the open-interior and closed-closure inequalities supplied by
Portmanteau; boundary-nullity then gives convergence of the sharp count. -/
theorem tendsto_rationalWindow_count_of_local_portmanteau
    {ι : Type*} {l : Filter ι}
    {νs : ι → FiniteMeasure (MarkedSpectralSpace Unit)}
    {ν : FiniteMeasure (MarkedSpectralSpace Unit)}
    (n : ℕ) (q : ℚ × ℚ)
    (hboundary : (ν : Measure _) (frontier
      (rationalWindowDeterminingFamily n q)) = 0)
    (hopen : (ν : Measure _) (interior
      (rationalWindowDeterminingFamily n q)) ≤
      l.liminf (fun i => (νs i : Measure _)
        (interior (rationalWindowDeterminingFamily n q))))
    (hclosed : l.limsup (fun i => (νs i : Measure _)
        (closure (rationalWindowDeterminingFamily n q))) ≤
      (ν : Measure _) (closure
        (rationalWindowDeterminingFamily n q))) :
    Tendsto (fun i => (νs i : Measure _)
        (rationalWindowDeterminingFamily n q)) l
      (𝓝 ((ν : Measure _)
        (rationalWindowDeterminingFamily n q))) := by
  apply tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
    interior_subset subset_closure
  · change (ν : Measure _) (closure
      (rationalWindowDeterminingFamily n q) \
        interior (rationalWindowDeterminingFamily n q)) = 0 at hboundary
    exact hboundary
  · exact hopen
  · exact hclosed

end CoareaNative.BlockBand
