module

public import BlockBand.PointProcess.Vague
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Finite atomic point and marked configurations

The finite counting measure of an indexed family of atoms (with multiplicity), as a sum of Dirac
masses, a vague point measure and a marked point measure.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {d : ℕ}

/-- Number of indexed atoms in a set, retaining multiplicities. -/
def finiteAtomicCount (locations : Fin d → X) (A : Set X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => locations i ∈ A)).card

/-- Pushforward of finite counting measure under the indexed atom map. -/
def finiteAtomicMeasure (locations : Fin d → X) : Measure X :=
  Measure.map locations Measure.count

omit [TopologicalSpace X] in
/-- Every measurable-set value equals the exact natural atom count. -/
theorem finiteAtomicMeasure_apply (locations : Fin d → X) (A : Set X)
    (hA : MeasurableSet A) :
    finiteAtomicMeasure locations A = (finiteAtomicCount locations A : ENNReal) := by
  classical
  let t := Finset.univ.filter (fun i => locations i ∈ A)
  have ht : locations ⁻¹' A = (t : Set (Fin d)) := by
    ext i
    simp [t]
  unfold finiteAtomicMeasure finiteAtomicCount
  rw [Measure.map_apply (measurable_of_finite locations) hA, ht, Measure.count_apply_finset]

omit [TopologicalSpace X] in
/-- The counting pushforward is exactly the finite sum of Dirac masses, including every atom
multiplicity. -/
theorem finiteAtomicMeasure_eq_sum_dirac (locations : Fin d → X) :
    finiteAtomicMeasure locations = ∑ i : Fin d, Measure.dirac (locations i) := by
  classical
  ext A hA
  rw [finiteAtomicMeasure_apply locations A hA]
  simp only [finiteAtomicCount, Measure.finsetSum_apply, hA, Measure.dirac_apply',
    Set.indicator_apply, Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

/-- Canonical finite point configuration, allowing repeated atoms. -/
def finiteAtomicPointMeasure (locations : Fin d → X) : VaguePointMeasure X where
  measure := finiteAtomicMeasure locations
  finite_on_compact := by
    intro K _
    apply lt_of_le_of_lt (measure_mono (Set.subset_univ K))
    rw [finiteAtomicMeasure_apply locations Set.univ MeasurableSet.univ]
    simp
  integer_valued := by
    intro A hA
    exact Or.inr ⟨finiteAtomicCount locations A, finiteAtomicMeasure_apply locations A hA⟩
  count := fun A => finiteAtomicCount locations A.carrier
  measure_eq_count := fun A => finiteAtomicMeasure_apply locations A.carrier A.measurable

/-- The finite marked configuration of an indexed family of marked atoms. -/
def finiteAtomicMarkedPointMeasure (locations : Fin d → MarkedSpectralSpace) :
    MarkedPointMeasure where
  marked := finiteAtomicPointMeasure locations
  spectral := finiteAtomicPointMeasure (fun i => (locations i).1)
  spectral_eq := by
    change Measure.map (fun i => (locations i).1) Measure.count =
      Measure.map Prod.fst (Measure.map locations Measure.count)
    rw [Measure.map_map measurable_fst (measurable_of_finite locations)]
    rfl

/-- The marked measure is exactly the finite counting pushforward. -/
theorem finiteAtomicMarkedPointMeasure_marked (locations : Fin d → MarkedSpectralSpace) :
    (finiteAtomicMarkedPointMeasure locations).marked.measure = finiteAtomicMeasure locations := rfl

end BlockBand.Model.Construction
