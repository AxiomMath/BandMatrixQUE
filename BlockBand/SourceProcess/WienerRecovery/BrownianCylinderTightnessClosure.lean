module

public import BlockBand.SourceProcess.WienerRecovery.ScalarWienerMeasureConstruction
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite-dimensional inputs for Brownian cylinder tightness

The Carathéodory construction in `ScalarWienerMeasureConstruction` reduces scalar
Wiener measure to continuity at the empty set of the Brownian cylinder content.
This module proves the finite-dimensional ingredients available directly from
Mathlib: exact Gaussian increment laws and compact inner approximation of every
finite-dimensional marginal event (`exists_compact_brownianProjectiveFamily_core`,
`exists_compact_base_subcylinder`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH
namespace BrownianCylinderTightnessClosure

open scoped NNReal Topology ENNReal
open Filter Set MeasureTheory ProbabilityTheory
open ScalarWienerRealizationClosure
open ScalarWienerMeasureConstruction

/-- Every Brownian finite-dimensional marginal is a probability measure, so in
particular every measurable event has finite mass. -/
theorem brownianProjectiveFamily_apply_ne_top
    (I : Finset NNReal) (S : Set (I → ℝ)) :
    BrownianReal.projectiveFamily I S ≠ ∞ := by
  exact measure_ne_top _ _

/-- Exact Gaussian increment law inside every finite Brownian marginal.  This
is the probabilistic input for the summable increment-tail bounds in the
chaining argument: the variance parameter is the nonnegative
distance `nndist s t`, with no extra factor. -/
theorem map_brownianProjectiveFamily_increment
    (I : Finset NNReal) (s t : I) :
    Measure.map (fun x : I → ℝ => x s - x t)
        (BrownianReal.projectiveFamily I) =
      gaussianReal 0 (nndist (s : NNReal) (t : NNReal)) :=
  (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I s t).map_eq

/-- Exact readback of every two-time increment tail to a one-dimensional
centered Gaussian tail.  Later dyadic chaining can therefore use scalar
Gaussian estimates without postulating a process on infinite path space. -/
theorem brownianProjectiveFamily_increment_tail_eq
    (I : Finset NNReal) (s t : I) (R : ℝ) :
    BrownianReal.projectiveFamily I
        {x | R ≤ |x s - x t|} =
      gaussianReal 0 (nndist (s : NNReal) (t : NNReal))
        {y | R ≤ |y|} := by
  rw [← map_brownianProjectiveFamily_increment I s t]
  rw [Measure.map_apply]
  · rfl
  · fun_prop
  · exact measurableSet_le measurable_const measurable_id.norm

/-- Compact inner approximation for a finite-dimensional Brownian
cylinder base.  The set `K` is both compact and closed, lies inside `S`, and
loses less than the prescribed positive `ENNReal` error.

This is the finite-dimensional Gaussian tightness input used in the classical
Kolmogorov extension proof.  No measure on the infinite raw path product is
used. -/
theorem exists_compact_brownianProjectiveFamily_core
    (I : Finset NNReal) {S : Set (I → ℝ)} (hS : MeasurableSet S)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set (I → ℝ), K ⊆ S ∧ IsCompact K ∧ IsClosed K ∧
      BrownianReal.projectiveFamily I (S \ K) < ε := by
  exact hS.exists_isCompact_isClosed_sdiff_lt
    (brownianProjectiveFamily_apply_ne_top I S) hε

/-- Every measurable Brownian cylinder therefore contains the lift of a compact
closed finite-dimensional core with arbitrarily small loss in its defining
marginal.  The lifted set is still a cylinder; it is not claimed compact in the
full uncountable product, which is why a simultaneous countable
compact-containment argument is needed. -/
theorem exists_compact_base_subcylinder
    {A : Set BrownianRawPath}
    (hA : A ∈ measurableCylinders (fun _ : NNReal => ℝ))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (I : Finset NNReal) (S K : Set (I → ℝ)),
      MeasurableSet S ∧ A = cylinder I S ∧ K ⊆ S ∧ IsCompact K ∧ IsClosed K ∧
        BrownianReal.projectiveFamily I (S \ K) < ε := by
  rcases (mem_measurableCylinders _).1 hA with ⟨I, S, hS, rfl⟩
  rcases exists_compact_brownianProjectiveFamily_core I hS hε with
    ⟨K, hKS, hKc, hKcl, hloss⟩
  exact ⟨I, S, K, hS, rfl, hKS, hKc, hKcl, hloss⟩

end BrownianCylinderTightnessClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
