module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeContinuousMartingale
public import BlockBand.SourceProcess.FiniteDriverCompletion.RefinedGridIntegral

/-!
# Algebraic relations of the continuous grid sums

The continuous finite-grid stochastic sums `continuousIntegral` are unchanged under contiguous
refinement of the grid, and are additive and homogeneous in the grid presentation.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open FiniteIto ContinuousItoCommonRefinement
namespace GridPresentation
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

omit [IsProbabilityMeasure μ] in
/-- The scalar stochastic sum telescopes over every parent fiber of a contiguous refinement. -/
theorem pullback_continuousScalarSum (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine)
    (a : κ) (u : ℝ≥0) (x : DriverSample S κ) :
    (∑ k : Fin n, (d.pullback r).continuousTerm k a u x) = ∑ i : Fin d.steps, d.continuousTerm i a u x := by
  have hsum : (∑ k : Fin n, (d.pullback r).continuousTerm k a u x) =
      ∑ k : Fin n, d.coeff (r.toGridRefinement.parent k) a x *
        (commonRealBrownian (min u (fine.time k.succ)) x a - commonRealBrownian (min u (fine.time k.castSucc)) x a) := by
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hsum]
  simp only [continuousTerm]
  let B : Fin (n + 1) → ℝ := fun j => commonRealBrownian (min u (fine.time j)) x a
  change (∑ k : Fin n, d.coeff (r.toGridRefinement.parent k) a x *
    (B k.succ - B k.castSucc)) = _
  rw [← Fintype.sum_fiberwise r.toGridRefinement.parent
    (fun k => d.coeff (r.toGridRefinement.parent k) a x * (B k.succ - B k.castSucc))]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      d.coeff i a x * (B k.val.succ - B k.val.castSucc) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [k.property]
    _ = d.coeff i a x * ∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      (B k.val.succ - B k.val.castSucc) := by rw [Finset.mul_sum]
    _ = _ := by rw [r.sum_path_increments B i]; simp only [B, r.endpoint_time]

omit [IsProbabilityMeasure μ] in
/-- The continuous stochastic sum is pointwise invariant under contiguous refinement. -/
theorem continuousIntegral_pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine) :
    (d.pullback r).continuousIntegral = d.continuousIntegral := by
  funext u x
  simp only [continuousIntegral]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i a => d.continuousTerm i a u x)]
  apply Finset.sum_congr rfl
  intro a _
  exact d.pullback_continuousScalarSum r a u x

omit [IsProbabilityMeasure μ] in
/-- Continuous sums add, through the common refinement of the two grids. -/
theorem continuousIntegral_add (d e : GridPresentation (κ := κ) μ T) :
    (d.add e).continuousIntegral = d.continuousIntegral + e.continuousIntegral := by
  let rd := leftCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  let re := rightCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  have hp : (d.add e).continuousIntegral =
      (d.pullback rd).continuousIntegral + (e.pullback re).continuousIntegral := by
    funext u x
    simp only [continuousIntegral, continuousTerm, add, rd, re, Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rfl
  rw [hp, d.continuousIntegral_pullback rd, e.continuousIntegral_pullback re]

omit [IsProbabilityMeasure μ] in
/-- Scalar multiplication acts pointwise on the continuous finite sum. -/
theorem continuousIntegral_smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) :
    (d.smul c).continuousIntegral = c • d.continuousIntegral := by
  funext u x
  simp only [continuousIntegral, continuousTerm, smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp_rw [Finset.mul_sum]
  rfl

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
