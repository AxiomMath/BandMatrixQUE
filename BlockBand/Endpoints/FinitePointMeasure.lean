module

public import BlockBand.PointProcess.Vague

/-!
# Finite point measures

We define the point measure `∑ i, δ_{x i}` of a finite family of points as an element of the vague
state space and compute integrals against it.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory
open scoped ENNReal Classical

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

omit [TopologicalSpace X] in
theorem finset_sum_dirac_apply {ι : Type*} [Fintype ι] (x : ι → X) {A : Set X}
    (hA : MeasurableSet A) :
    (∑ i, Measure.dirac (x i)) A = ((Finset.univ.filter fun i => x i ∈ A).card : ℝ≥0∞) := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ hA, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The finite point measure `∑ i, δ_{x i}` in the vague state space. -/
def finitePointMeasure {ι : Type*} [Fintype ι] (x : ι → X) : VaguePointMeasure X where
  measure := ∑ i, Measure.dirac (x i)
  finite_on_compact K _ := by
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _
  integer_valued A hA := Or.inr ⟨_, finset_sum_dirac_apply x hA⟩
  count A := (Finset.univ.filter fun i => x i ∈ A.carrier).card
  measure_eq_count A := finset_sum_dirac_apply x A.measurable

theorem finitePointMeasure_measure {ι : Type*} [Fintype ι] (x : ι → X) :
    (finitePointMeasure x).measure = ∑ i, Measure.dirac (x i) := rfl

theorem finitePointMeasure_measure_apply {ι : Type*} [Fintype ι] (x : ι → X) {A : Set X}
    (hA : MeasurableSet A) :
    (finitePointMeasure x).measure A =
      ((Finset.univ.filter fun i => x i ∈ A).card : ℝ≥0∞) :=
  finset_sum_dirac_apply x hA

/-- Integration against a finite point measure is the finite sum of the values. -/
theorem integral_finitePointMeasure [OpensMeasurableSpace X] {ι : Type*} [Fintype ι]
    (x : ι → X) (g : X → ℝ) (hg : Continuous g) :
    ∫ y, g y ∂(finitePointMeasure x).measure = ∑ i, g (x i) := by
  rw [finitePointMeasure_measure, integral_finsetSum_measure]
  · exact Finset.sum_congr rfl fun i _ =>
      integral_dirac' g (x i) hg.measurable.stronglyMeasurable
  · intro i _
    exact integrable_dirac' hg.measurable.stronglyMeasurable enorm_lt_top

theorem coordinate_finitePointMeasure [OpensMeasurableSpace X] {ι : Type*} [Fintype ι]
    (x : ι → X) (g : CompactlySupportedContinuousMap X ℝ) :
    (finitePointMeasure x).coordinate g = ∑ i, g (x i) :=
  integral_finitePointMeasure x g g.continuous

end BlockBand.Endpoints
