module

public import BlockBand.Model.Construction.SpectralAtomic
public import BlockBand.Model.Construction.SpectralMarkSingleton

/-!
# Continuity of finite configurations in the vague topology

The map from the locations of `d` atoms to the finite atomic point measure, and to the finite
marked point measure, is continuous for the vague topology.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

/-- Exact compact-continuous-test coordinate of a finite atom configuration. -/
theorem finiteAtomicPointMeasure_coordinate {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [MeasurableSingletonClass X] {d : ℕ}
    (locations : Fin d → X) (f : CompactlySupportedContinuousMap X ℝ) :
    (finiteAtomicPointMeasure locations).coordinate f = ∑ i, f (locations i) := by
  change (∫ x, f x ∂finiteAtomicMeasure locations) = _
  rw [finiteAtomicMeasure_eq_sum_dirac,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

/-- The finite atom map is continuous for the vague topology. -/
theorem continuous_finiteAtomicPointMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (d : ℕ) :
    Continuous (finiteAtomicPointMeasure (X := X) (d := d)) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  simp_rw [Function.comp_apply, finiteAtomicPointMeasure_coordinate]
  apply continuous_finsetSum
  intro i _
  exact f.continuous.comp (continuous_apply i)

/-- The finite marked atom map is continuous; it uses the measurable singletons of the space of
torus mass profiles. -/
theorem continuous_finiteAtomicMarkedPointMeasure (d : ℕ) :
    Continuous (finiteAtomicMarkedPointMeasure (d := d)) := by
  let : MeasurableSingletonClass MassProfile := massProfile_measurableSingletonClass
  rw [continuous_induced_rng]
  change Continuous (finiteAtomicPointMeasure (X := MarkedSpectralSpace) (d := d))
  exact continuous_finiteAtomicPointMeasure d

end BlockBand.Model.Construction
