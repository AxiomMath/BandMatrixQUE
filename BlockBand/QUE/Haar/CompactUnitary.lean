module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.Bases

/-!
# The Haar probability measure on the compact unitary group

The unitary group `U(A)` is compact (closed with entries bounded by one); its Haar measure
normalized on the whole group is a probability measure invariant under left translation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open MeasureTheory MeasureTheory.Measure Matrix
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every column of a finite unitary matrix has total squared mass one. -/
theorem unitary_column_mass (U : Matrix.unitaryGroup A ℂ) (a : A) :
    (∑ c : A, ‖U c a‖ ^ 2) = 1 := by
  have h := congrArg (fun M : Matrix A A ℂ => (M a a).re)
    (Matrix.UnitaryGroup.star_mul_self U)
  simpa [Matrix.mul_apply, star, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply, Complex.sq_norm,
    mul_comm, ← pow_two] using h

/-- A finite unitary entry has absolute value at most one. -/
theorem unitary_entry_norm_le (U : Matrix.unitaryGroup A ℂ) (c a : A) :
    ‖U c a‖ ≤ 1 := by
  have hsq : ‖U c a‖ ^ 2 ≤ 1 := by
    rw [← unitary_column_mass U a]
    exact Finset.single_le_sum (fun d _ => sq_nonneg ‖U d a‖) (Finset.mem_univ c)
  nlinarith [norm_nonneg (U c a)]

/-- The unitary group is compact, by closedness and the uniform entry bound. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup A ℂ : Set (Matrix A A ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset
    (isClosed_unitary (R := Matrix A A ℂ))
  intro M hM c a
  simpa using unitary_entry_norm_le ⟨M, hM⟩ c a

instance compactSpaceUnitary : CompactSpace (Matrix.unitaryGroup A ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

instance secondCountableUnitary : SecondCountableTopology (Matrix.unitaryGroup A ℂ) := by
  have : SecondCountableTopology (Matrix A A ℂ) :=
    inferInstanceAs (SecondCountableTopology (A → A → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology (Matrix.unitaryGroup A ℂ : Set (Matrix A A ℂ))

/-- The whole compact unitary group is the normalization set. -/
def unitaryNormalization : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup A ℂ) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar measure with total mass one, constructed from compactness. -/
def unitaryProbability : Measure (Matrix.unitaryGroup A ℂ) :=
  MeasureTheory.Measure.haarMeasure unitaryNormalization

instance probabilityUnitary : IsProbabilityMeasure (unitaryProbability (A := A)) where
  measure_univ := MeasureTheory.Measure.haarMeasure_self (K₀ := unitaryNormalization)

instance invariantUnitary :
    IsMulLeftInvariant (unitaryProbability (A := A)) := by
  unfold unitaryProbability
  infer_instance

/-- Left translation preserves integrals for this constructed probability law. -/
theorem integral_unitary_translate (f : Matrix.unitaryGroup A ℂ → ℝ)
    (V : Matrix.unitaryGroup A ℂ) :
    (∫ U, f (V * U) ∂unitaryProbability) = ∫ U, f U ∂unitaryProbability :=
  integral_mul_left_eq_self f V

end BlockBand.QUE.Haar
