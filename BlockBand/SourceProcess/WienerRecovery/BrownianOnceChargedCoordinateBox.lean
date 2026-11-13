module

public import BlockBand.SourceProcess.WienerRecovery.BrownianNestedCompactCoreProof
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Once-charged compact coordinate boxes for Brownian cylinders

This module constructs the global-box part of
`BrownianCylinderOnceChargedCompactCore` without a path-space measure or a
continuity-at-empty assumption.  The countable union of all finite cylinder
supports is used as the index type for a summable family of Gaussian tail
budgets.  Inner regularity of each exact one-coordinate Gaussian marginal
then supplies one compact nonempty fiber per used coordinate.  A finite union
bound proves that escape from every cumulative finite-support box costs less
than the single prescribed global budget.

The inside-box compact approximation of each measurable base, with summable stage
losses `δ n`, is not part of this module; the two parts are combined in
`brownianCylinderOnceChargedCompactCore`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH
namespace BrownianOnceChargedCoordinateBox

open scoped NNReal Topology ENNReal
open Filter Set MeasureTheory ProbabilityTheory
open ScalarWienerRealizationClosure
open ScalarWienerMeasureConstruction
open BrownianCylinderTightnessClosure
open BrownianNestedCompactCoreProof

/-- The countable set of all coordinates occurring in a sequence of finite
cylinder supports. -/
def globalCylinderSupport (I : ℕ → Finset NNReal) : Set NNReal :=
  ⋃ n, (I n : Set NNReal)

/-- A countable union of finite cylinder supports is countable. -/
theorem countable_globalCylinderSupport (I : ℕ → Finset NNReal) :
    (globalCylinderSupport I).Countable := by
  apply Set.countable_iUnion
  intro n
  exact (I n).finite_toSet.countable

/-- The finite union of the supports used through stage `n`. -/
def cumulativeCylinderSupport (I : ℕ → Finset NNReal) (n : ℕ) : Finset NNReal :=
  (Finset.range (n + 1)).biUnion I

/-- Every cumulative support coordinate belongs to the global support. -/
theorem cumulativeCylinderSupport_subset_global
    (I : ℕ → Finset NNReal) (n : ℕ) :
    (cumulativeCylinderSupport I n : Set NNReal) ⊆ globalCylinderSupport I := by
  intro t ht
  simp only [cumulativeCylinderSupport, Finset.mem_coe, Finset.mem_biUnion] at ht
  rcases ht with ⟨j, hj, htj⟩
  exact Set.mem_iUnion.2 ⟨j, htj⟩

/-- The universal raw-path set is a measurable cylinder. -/
theorem univ_mem_measurableCylinders :
    (Set.univ : Set BrownianRawPath) ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
  rw [show (Set.univ : Set BrownianRawPath) =
    cylinder (∅ : Finset NNReal) Set.univ by ext; rfl]
  apply cylinder_mem_measurableCylinders
  exact MeasurableSet.univ

/-- The one-coordinate escape cylinder from a prescribed fiber. -/
def coordinateEscapeCylinder (q : NNReal → Set ℝ) (t : NNReal) :
    Set BrownianRawPath :=
  cylinder ({t} : Finset NNReal)
    {x | x ⟨t, by simp⟩ ∉ q t}

/-- Exact one-coordinate readback of a compact-fiber escape event to its
centered Gaussian marginal. -/
theorem brownianCylinderContent_coordinateEscapeCylinder
    {q : NNReal → Set ℝ} (hq : ∀ t, IsClosed (q t)) (t : NNReal) :
    brownianCylinderContent (coordinateEscapeCylinder q t) =
      gaussianReal 0 t ((q t)ᶜ) := by
  let s : ({t} : Finset NNReal) := ⟨t, by simp⟩
  have hbase : MeasurableSet
      ({x : ({t} : Finset NNReal) → ℝ | x s ∉ q t}) := by
    exact (hq t).measurableSet.compl.preimage (measurable_pi_apply s)
  rw [coordinateEscapeCylinder,
    brownianCylinderContent_cylinder ({t} : Finset NNReal) _ hbase]
  have hmap := (BrownianReal.measurePreserving_eval_projectiveFamily s).measure_preimage
    (hq t).measurableSet.compl.nullMeasurableSet
  change BrownianReal.projectiveFamily ({t} : Finset NNReal)
      ((fun x => x s) ⁻¹' (q t)ᶜ) = gaussianReal 0 t ((q t)ᶜ)
  simpa [s] using hmap

/-- Escape from the cumulative box is contained in the finite union of the
one-coordinate escape cylinders indexed by the cumulative support. -/
theorem cumulativeLiftedBox_compl_subset_coordinateEscapes
    (I : ℕ → Finset NNReal) (q : NNReal → Set ℝ) (n : ℕ) :
    (cumulativeLiftedBox I q n)ᶜ ⊆
      ⋃ t ∈ cumulativeCylinderSupport I n, coordinateEscapeCylinder q t := by
  intro ω hω
  simp only [cumulativeLiftedBox, Set.mem_compl_iff, Set.mem_iInter,
    not_forall] at hω
  rcases hω with ⟨j, hj⟩
  rcases hj with ⟨hjrange, hjbox⟩
  change (fun i : I j => ω i) ∉ finiteCoordinateCompactBox q (I j) at hjbox
  simp only [finiteCoordinateCompactBox, Set.mem_pi, Set.mem_univ, forall_const,
    not_forall] at hjbox
  rcases hjbox with ⟨i, hi⟩
  have hit : (i : NNReal) ∈ cumulativeCylinderSupport I n := by
    simp only [cumulativeCylinderSupport, Finset.mem_biUnion]
    exact ⟨j, hjrange, i.property⟩
  refine Set.mem_iUnion.2 ⟨(i : NNReal), Set.mem_iUnion.2 ⟨hit, ?_⟩⟩
  exact hi

/-- Finite union bound for escape from a cumulative coordinate box. -/
theorem brownianCylinderContent_cumulativeLiftedBox_compl_le
    (I : ℕ → Finset NNReal) {q : NNReal → Set ℝ}
    (hq : ∀ t, IsCompact (q t)) (n : ℕ) :
    brownianCylinderContent ((cumulativeLiftedBox I q n)ᶜ) ≤
      ∑ t ∈ cumulativeCylinderSupport I n, gaussianReal 0 t ((q t)ᶜ) := by
  have hEscapeMem : ∀ t, coordinateEscapeCylinder q t ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    intro t
    apply cylinder_mem_measurableCylinders
    exact (hq t).isClosed.measurableSet.compl.preimage (measurable_pi_apply _)
  have hBoxMem : cumulativeLiftedBox I q n ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    apply isSetRing_measurableCylinders.biInter_mem (Finset.range (n + 1))
    · exact ⟨0, by simp⟩
    · intro j hj
      apply cylinder_mem_measurableCylinders
      have hcompact : IsCompact (finiteCoordinateCompactBox q (I j)) := by
        simpa [finiteCoordinateCompactBox, Set.pi] using
          (isCompact_pi_infinite fun i : I j => hq i)
      exact hcompact.isClosed.measurableSet
  calc
    brownianCylinderContent ((cumulativeLiftedBox I q n)ᶜ) ≤
        brownianCylinderContent
          (⋃ t ∈ cumulativeCylinderSupport I n, coordinateEscapeCylinder q t) :=
      addContent_mono isSetSemiring_measurableCylinders
        (by
          rw [show (cumulativeLiftedBox I q n)ᶜ =
            Set.univ \ cumulativeLiftedBox I q n by ext; simp]
          exact isSetRing_measurableCylinders.sdiff_mem
            univ_mem_measurableCylinders hBoxMem)
        (isSetRing_measurableCylinders.biUnion_mem _ fun t _ => hEscapeMem t)
        (cumulativeLiftedBox_compl_subset_coordinateEscapes I q n)
    _ ≤ ∑ t ∈ cumulativeCylinderSupport I n,
        brownianCylinderContent (coordinateEscapeCylinder q t) :=
      addContent_biUnion_le isSetRing_measurableCylinders
        (fun t _ => hEscapeMem t)
    _ = ∑ t ∈ cumulativeCylinderSupport I n,
        gaussianReal 0 t ((q t)ᶜ) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact brownianCylinderContent_coordinateEscapeCylinder (fun t => (hq t).isClosed) t

/-- Construction of compact nonempty coordinate fibers whose escape from every
finite cumulative support costs less than one prescribed global budget.

The budget is indexed by the countable subtype of coordinates that occur in some `I n`,
so repeated appearances of a coordinate are charged only once. -/
theorem exists_compact_coordinateFibers_global_box_loss
    (I : ℕ → Finset NNReal) {β : ℝ≥0∞} (hβ : β ≠ 0) :
    ∃ q : NNReal → Set ℝ,
      (∀ t, IsCompact (q t)) ∧
      (∀ t, (q t).Nonempty) ∧
      (∀ n, brownianCylinderContent ((cumulativeLiftedBox I q n)ᶜ) < β) := by
  classical
  let D : Set NNReal := globalCylinderSupport I
  let _ : Countable D := (countable_globalCylinderSupport I).to_subtype
  obtain ⟨ε, hεpos, hεsum⟩ := ENNReal.exists_pos_sum_of_countable' hβ D
  have hcore : ∀ t : D, ∃ K : Set ℝ,
      IsCompact K ∧ gaussianReal 0 (t : NNReal) (Kᶜ) < ε t := by
    intro t
    obtain ⟨K, hKuniv, hKcompact, hKclosed, hKloss⟩ :=
      exists_compact_brownianProjectiveFamily_core
        ({(t : NNReal)} : Finset NNReal) MeasurableSet.univ (hεpos t).ne'
    let s : ({(t : NNReal)} : Finset NNReal) := ⟨t, by simp⟩
    let L : Set ℝ := (fun x => x s) '' K
    have hLcompact : IsCompact L := hKcompact.image (continuous_apply s)
    have htail : gaussianReal 0 (t : NNReal) (Lᶜ) ≤
        BrownianReal.projectiveFamily ({(t : NNReal)} : Finset NNReal) (Set.univ \ K) := by
      rw [← (BrownianReal.measurePreserving_eval_projectiveFamily s).measure_preimage
        hLcompact.isClosed.measurableSet.compl.nullMeasurableSet]
      apply measure_mono
      intro x hx
      refine ⟨Set.mem_univ x, ?_⟩
      intro hxK
      exact hx ⟨x, hxK, rfl⟩
    exact ⟨L, hLcompact, htail.trans_lt hKloss⟩
  choose K hKcompact hKloss using hcore
  let q : NNReal → Set ℝ := fun t =>
    if ht : t ∈ D then K ⟨t, ht⟩ ∪ {0} else {0}
  have hqcompact : ∀ t, IsCompact (q t) := by
    intro t
    simp only [q]
    split_ifs with ht
    · exact (hKcompact ⟨t, ht⟩).union isCompact_singleton
    · exact isCompact_singleton
  have hqnonempty : ∀ t, (q t).Nonempty := by
    intro t
    refine ⟨0, ?_⟩
    by_cases ht : t ∈ D <;> simp [q, ht]
  refine ⟨q, hqcompact, hqnonempty, ?_⟩
  intro n
  let budget : NNReal → ℝ≥0∞ := fun t =>
    if ht : t ∈ D then ε ⟨t, ht⟩ else 0
  have htail : ∀ (t : NNReal) (ht : t ∈ cumulativeCylinderSupport I n),
      gaussianReal 0 t ((q t)ᶜ) ≤ budget t := by
    intro t ht
    have htD : t ∈ D := cumulativeCylinderSupport_subset_global I n ht
    change gaussianReal 0 t
      (((if _h : t ∈ D then K ⟨t, _h⟩ ∪ {0} else {0}) : Set ℝ)ᶜ) ≤
        (if _h : t ∈ D then ε ⟨t, _h⟩ else 0)
    simp only [dite_eq_left htD]
    exact (measure_mono (compl_subset_compl.mpr Set.subset_union_left)).trans
      (hKloss ⟨t, htD⟩).le
  calc
    brownianCylinderContent ((cumulativeLiftedBox I q n)ᶜ) ≤
        ∑ t ∈ cumulativeCylinderSupport I n, gaussianReal 0 t ((q t)ᶜ) :=
      brownianCylinderContent_cumulativeLiftedBox_compl_le I hqcompact n
    _ ≤ ∑ t ∈ cumulativeCylinderSupport I n, budget t := by
      gcongr with t ht
      exact htail t ht
    _ = ∑' t : (cumulativeCylinderSupport I n : Set NNReal), budget t := by
      rw [Finset.tsum_subtype']
    _ = ∑' t : (cumulativeCylinderSupport I n : Set NNReal),
        ε ⟨t, cumulativeCylinderSupport_subset_global I n t.property⟩ := by
      apply tsum_congr
      intro t
      simp [budget, D, cumulativeCylinderSupport_subset_global I n t.property]
    _ ≤ ∑' t : D, ε t := by
      let f : {t : NNReal // t ∈ cumulativeCylinderSupport I n} → D := fun t =>
        ⟨(t : NNReal), cumulativeCylinderSupport_subset_global I n t.property⟩
      exact ENNReal.tsum_comp_le_tsum_of_injective (f := f)
        (fun a b hab => Subtype.ext (congrArg (fun x : D => (x : NNReal)) hab)) ε
    _ < β := hεsum

/-- The constructed global fibers give exactly the once-charged box-loss field
needed by a cylinder sequence, independently of its measurable bases. -/
theorem exists_onceCharged_global_box_data
    (A : ℕ → Set BrownianRawPath)
    (hAcyl : ∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ))
    (I : ℕ → Finset NNReal) {β : ℝ≥0∞} (hβ : β ≠ 0) :
    ∃ q : NNReal → Set ℝ,
      (∀ t, IsCompact (q t)) ∧
      (∀ t, (q t).Nonempty) ∧
      (∀ n, brownianCylinderContent (A n \ cumulativeLiftedBox I q n) ≤ β) := by
  obtain ⟨q, hqc, hqn, hloss⟩ :=
    exists_compact_coordinateFibers_global_box_loss I hβ
  refine ⟨q, hqc, hqn, ?_⟩
  intro n
  have hBoxMem : cumulativeLiftedBox I q n ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    apply isSetRing_measurableCylinders.biInter_mem (Finset.range (n + 1))
    · exact ⟨0, by simp⟩
    · intro j hj
      apply cylinder_mem_measurableCylinders
      have hcompact : IsCompact (finiteCoordinateCompactBox q (I j)) := by
        simpa [finiteCoordinateCompactBox, Set.pi] using
          (isCompact_pi_infinite fun i : I j => hqc i)
      exact hcompact.isClosed.measurableSet
  have hdiff := isSetRing_measurableCylinders.sdiff_mem (hAcyl n) hBoxMem
  have hcompl : (cumulativeLiftedBox I q n)ᶜ ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    rw [show (cumulativeLiftedBox I q n)ᶜ =
      Set.univ \ cumulativeLiftedBox I q n by ext; simp]
    exact isSetRing_measurableCylinders.sdiff_mem
      univ_mem_measurableCylinders hBoxMem
  exact (addContent_mono isSetSemiring_measurableCylinders hdiff hcompl
    (by intro x hx; exact hx.2)).trans (hloss n).le

end BrownianOnceChargedCoordinateBox
end BlockBand.SourceProcess.WienerRecovery.CEH
