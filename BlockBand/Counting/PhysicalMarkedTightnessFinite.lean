module
public import BlockBand.Counting.PhysicalMarkedTightnessCompact
public import BlockBand.Model.Construction.SpectralAtomic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite marked configurations as shell arrays

A finite indexed family of marked atoms is enumerated shell by shell into a padded shell
array.  The resulting marked point measure equals the original finite atomic measure, with
multiplicities, so every finite configuration whose shell occupation respects the caps lies
in the compact set `markedShellCompactSet caps`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set
open scoped Topology ENNReal NNReal
local instance (caps : ℕ → ℕ) : MeasurableSpace (MarkedShellIndex caps) := ⊤
local instance (caps : ℕ → ℕ) : MeasurableSingletonClass (MarkedShellIndex caps) :=
  ⟨fun _ => by trivial⟩

/-- Unique shell assignment, including atoms on integer boundaries. -/
def markedAtomShellNumber (z : MarkedSpectralSpace) : ℕ := Nat.floor |z.1|

theorem markedAtom_mem_assignedShell (z : MarkedSpectralSpace) :
    z ∈ markedAtomShell (markedAtomShellNumber z) := by
  exact ⟨Nat.floor_le (abs_nonneg _), (Nat.lt_floor_add_one |z.1|).le⟩

/-- Finite labels in the unique assigned shell, counting repeated locations separately. -/
def finiteMarkedShellLabels {d : ℕ} (locations : Fin d → MarkedSpectralSpace) (j : ℕ) :
    Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun i => markedAtomShellNumber (locations i) = j)

theorem mem_finiteMarkedShellLabels {d : ℕ} (locations : Fin d → MarkedSpectralSpace)
    (j : ℕ) (i : Fin d) : i ∈ finiteMarkedShellLabels locations j ↔
      markedAtomShellNumber (locations i) = j := by
  classical
  simp [finiteMarkedShellLabels]

/-- Padded enumeration of all indexed atoms shell by shell. -/
def finiteMarkedShellArray {d : ℕ} (locations : Fin d → MarkedSpectralSpace)
    (caps : ℕ → ℕ) : MarkedShellArray caps := by
  classical
  intro j k
  let s := finiteMarkedShellLabels locations j
  if h : k.val < s.card then
    let i := s.equivFin.symm ⟨k.val, h⟩
    exact Sum.inr ⟨locations i.val, by
      have hj := (mem_finiteMarkedShellLabels locations j i.val).mp i.property
      simpa only [hj] using markedAtom_mem_assignedShell (locations i.val)⟩
  else
    exact Sum.inl ()

/-- The unique padded cell occupied by an indexed atom, under the shell caps. -/
def finiteMarkedShellIndex {d : ℕ} (locations : Fin d → MarkedSpectralSpace)
    (caps : ℕ → ℕ) (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j)
    (i : Fin d) : MarkedShellIndex caps := by
  classical
  let j := markedAtomShellNumber (locations i)
  let s := finiteMarkedShellLabels locations j
  have hi : i ∈ s := (mem_finiteMarkedShellLabels locations j i).mpr rfl
  let k := s.equivFin ⟨i, hi⟩
  exact ⟨j, ⟨k.val, k.isLt.trans_le (hcap j)⟩⟩

/-- Decode a padded cell to its original indexed label, or no label if inactive. -/
def finiteMarkedShellDecode {d : ℕ} (locations : Fin d → MarkedSpectralSpace)
    (caps : ℕ → ℕ) (k : MarkedShellIndex caps) : Option (Fin d) := by
  classical
  let s := finiteMarkedShellLabels locations k.1
  if h : k.2.val < s.card then
    exact some (s.equivFin.symm ⟨k.2.val, h⟩).val
  else
    exact none

theorem finiteMarkedShellDecode_index {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) (i : Fin d) :
    finiteMarkedShellDecode locations caps (finiteMarkedShellIndex locations caps hcap i) = some i := by
  classical
  let s := finiteMarkedShellLabels locations (markedAtomShellNumber (locations i))
  have hi : i ∈ s := (mem_finiteMarkedShellLabels locations _ i).mpr rfl
  change (if h : (s.equivFin ⟨i, hi⟩).val < s.card then
      some (s.equivFin.symm ⟨(s.equivFin ⟨i, hi⟩).val, h⟩).val else none) = some i
  rw [dite_eq_left (s.equivFin ⟨i, hi⟩).isLt]
  change some (s.equivFin.symm (s.equivFin ⟨i, hi⟩)).val = some i
  rw [Equiv.symm_apply_apply]

theorem finiteMarkedShellIndex_injective {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) :
    Function.Injective (finiteMarkedShellIndex locations caps hcap) := by
  intro i i' he
  apply Option.some.inj
  rw [← finiteMarkedShellDecode_index locations caps hcap i,
    ← finiteMarkedShellDecode_index locations caps hcap i']
  exact congrArg (finiteMarkedShellDecode locations caps) he

/-- Every original indexed atom appears in its padded cell with its unchanged mark. -/
theorem finiteMarkedShellArray_at_index {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) (i : Fin d) :
    markedShellLocation (finiteMarkedShellArray locations caps)
        (finiteMarkedShellIndex locations caps hcap i) = locations i ∧
      finiteMarkedShellIndex locations caps hcap i ∈
        markedShellActive (finiteMarkedShellArray locations caps) := by
  classical
  unfold finiteMarkedShellIndex
  dsimp only
  let s := finiteMarkedShellLabels locations (markedAtomShellNumber (locations i))
  have hi : i ∈ s := (mem_finiteMarkedShellLabels locations _ i).mpr rfl
  have hk : (s.equivFin ⟨i, hi⟩).val < s.card := (s.equivFin ⟨i, hi⟩).isLt
  constructor
  · simp [markedShellLocation, finiteMarkedShellArray, s, hk]
  · simp [markedShellActive, finiteMarkedShellArray, s, hk]
    exact ⟨(locations i).1, (locations i).2, markedAtom_mem_assignedShell (locations i), rfl⟩

/-- Active padded cells are exactly cells that enumerate an original atom label. -/
theorem finiteMarkedShellArray_active_iff {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ) (k : MarkedShellIndex caps) :
    k ∈ markedShellActive (finiteMarkedShellArray locations caps) ↔
      k.2.val < (finiteMarkedShellLabels locations k.1).card := by
  classical
  by_cases h : k.2.val < (finiteMarkedShellLabels locations k.1).card
  · simp [markedShellActive, finiteMarkedShellArray, h]
    let i := (finiteMarkedShellLabels locations k.1).equivFin.symm ⟨k.2.val, h⟩
    have hj := (mem_finiteMarkedShellLabels locations k.1 i.val).mp i.property
    refine ⟨(locations i.val).1, (locations i.val).2, ?_, rfl⟩
    simpa only [hj] using markedAtom_mem_assignedShell (locations i.val)
  · simp [markedShellActive, finiteMarkedShellArray, h]

/-- The active-cell set is exactly the injective image of the finite original label set. -/
theorem finiteMarkedShellArray_active_eq_range {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) :
    markedShellActive (finiteMarkedShellArray locations caps) =
      Set.range (finiteMarkedShellIndex locations caps hcap) := by
  classical
  ext k
  constructor
  · intro hk
    have h := (finiteMarkedShellArray_active_iff locations caps k).mp hk
    let s := finiteMarkedShellLabels locations k.1
    let i := s.equivFin.symm ⟨k.2.val, h⟩
    have hj : markedAtomShellNumber (locations i.val) = k.1 :=
      (mem_finiteMarkedShellLabels locations k.1 i.val).mp i.property
    refine ⟨i.val, Sigma.ext hj ?_⟩
    apply (Fin.heq_ext_iff (congrArg caps hj)).mpr
    have hrank : ∀ (j : ℕ) (hi : i.val ∈ finiteMarkedShellLabels locations j),
        j = k.1 → ((finiteMarkedShellLabels locations j).equivFin ⟨i.val, hi⟩).val = k.2.val := by
      intro j hi hje
      subst j
      change (s.equivFin i).val = k.2.val
      dsimp only [i]
      rw [Equiv.apply_symm_apply]
    exact hrank _ _ hj
  · rintro ⟨i, rfl⟩
    exact (finiteMarkedShellArray_at_index locations caps hcap i).2

/-- Exact measure identity, with every multiplicity retained, between the padded
array and the original finite marked atom measure. -/
theorem finiteMarkedShellArray_measure {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) :
    markedShellCountingMeasure (finiteMarkedShellArray locations caps) =
      BlockBand.Model.Construction.finiteAtomicMeasure locations := by
  classical
  ext A hA
  rw [markedShellCountingMeasure_apply _ A hA,
    BlockBand.Model.Construction.finiteAtomicMeasure,
    Measure.map_apply (measurable_of_finite _) hA]
  let e := finiteMarkedShellIndex locations caps hcap
  have heq : (markedShellLocation (finiteMarkedShellArray locations caps) ⁻¹' A) ∩
      markedShellActive (finiteMarkedShellArray locations caps) = e '' (locations ⁻¹' A) := by
    ext k
    constructor
    · rintro ⟨hA', hk⟩
      rw [finiteMarkedShellArray_active_eq_range locations caps hcap] at hk
      obtain ⟨i, rfl⟩ := hk
      refine ⟨i, ?_, rfl⟩
      change markedShellLocation (finiteMarkedShellArray locations caps)
        (finiteMarkedShellIndex locations caps hcap i) ∈ A at hA'
      rw [(finiteMarkedShellArray_at_index locations caps hcap i).1] at hA'
      exact hA'
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, (finiteMarkedShellArray_at_index locations caps hcap i).2⟩
      change markedShellLocation (finiteMarkedShellArray locations caps)
        (finiteMarkedShellIndex locations caps hcap i) ∈ A
      rw [(finiteMarkedShellArray_at_index locations caps hcap i).1]
      exact hi
  rw [heq, Measure.count_apply (Set.to_countable _).measurableSet,
    Measure.count_apply (Set.to_countable _).measurableSet,
    (finiteMarkedShellIndex_injective locations caps hcap).encard_image]

/-- Every finite marked configuration with these shell caps belongs to
the compact set `markedShellCompactSet caps`. -/
theorem finiteAtomicMarked_mem_markedShellCompactSet {d : ℕ}
    (locations : Fin d → MarkedSpectralSpace) (caps : ℕ → ℕ)
    (hcap : ∀ j, (finiteMarkedShellLabels locations j).card ≤ caps j) :
    BlockBand.Model.Construction.finiteAtomicMarkedPointMeasure locations ∈
      markedShellCompactSet caps := by
  refine ⟨finiteMarkedShellArray locations caps, ?_⟩
  apply BlockBand.Model.Construction.markedPointMeasure_eq_of_marked_measure_eq
  exact finiteMarkedShellArray_measure locations caps hcap

end BlockBand.Counting
