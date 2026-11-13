module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridIntegral

/-!
# Refinement, sums and scalar multiples of grid presentations

A grid presentation pulls back to any contiguous refinement of its grid without changing its
stochastic sum; two presentations add through the common refinement of their grids, and the
stochastic sum and its `L²` class are additive and homogeneous.
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

theorem integralLp_coeFn (d : GridPresentation (κ := κ) μ T) :
    (d.integralLp : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ] d.integral :=
  d.integral_memLp.coeFn_toLp

/-- The pullback of a grid presentation to a contiguous refinement of its grid. -/
def pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ} {fine : TimeGrid n}
    (r : ContiguousGridRefinement d.grid fine) : GridPresentation (κ := κ) μ T where
  steps := n
  grid := fine
  initial_time := by rw [← d.initial_time, ← r.endpoint_time 0, r.endpoint_zero]
  terminal_time := by rw [← d.terminal_time, ← r.endpoint_time (Fin.last d.steps), r.endpoint_last]
  coeff := fun k => d.coeff (r.toGridRefinement.parent k)
  adapted := by
    intro k a
    apply (d.adapted (r.toGridRefinement.parent k) a).mono _ le_rfl
    apply (commonWienerFiltration S κ).mono
    rw [← r.endpoint_time]
    exact fine.strictMono_time.monotone (r.parent_interval k).1
  coeffL2 := fun k a => d.coeffL2 _ a

omit [IsProbabilityMeasure μ] in
/-- The scalar stochastic sum telescopes over every parent fiber. -/
theorem pullback_scalarSum (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine)
    (a : κ) (x : DriverSample S κ) :
    (∑ k : Fin n, (d.pullback r).term k a x) = ∑ i : Fin d.steps, d.term i a x := by
  have hsum : (∑ k : Fin n, (d.pullback r).term k a x) =
      ∑ k : Fin n, d.coeff (r.toGridRefinement.parent k) a x *
        (commonRealBrownian (fine.time k.succ) x a - commonRealBrownian (fine.time k.castSucc) x a) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (d.pullback r).term_apply k a x
  rw [hsum]
  simp only [term_apply]
  let B : Fin (n + 1) → ℝ := fun j => commonRealBrownian (fine.time j) x a
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
/-- The stochastic sum is pointwise invariant under contiguous refinement. -/
theorem integral_pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine) :
    (d.pullback r).integral = d.integral := by
  funext x
  simp only [integral, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i a => d.term i a x)]
  apply Finset.sum_congr rfl
  intro a _
  exact d.pullback_scalarSum r a x

/-- The `L²` class of the stochastic sum is invariant under refinement. -/
theorem integralLp_pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine) :
    (d.pullback r).integralLp = d.integralLp := by
  apply Lp.ext
  filter_upwards [(d.pullback r).integralLp_coeFn,
    d.integralLp_coeFn] with x hx hy
  rw [hx, hy, d.integral_pullback r]

/-- The sum of two presentations, on the common refinement of their grids. -/
def add (d e : GridPresentation (κ := κ) μ T) : GridPresentation (κ := κ) μ T := by
  let rd := leftCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  let re := rightCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  let d' := d.pullback rd
  let e' := e.pullback re
  exact { steps := commonStepCount d.grid e.grid
          grid := commonTimeGrid d.grid e.grid
          initial_time := d'.initial_time
          terminal_time := d'.terminal_time
          coeff := fun k a x => d'.coeff k a x + e'.coeff k a x
          adapted := fun k a => (d'.adapted k a).add (e'.adapted k a)
          coeffL2 := fun k a => (d'.coeffL2 k a).add (e'.coeffL2 k a) }

omit [IsProbabilityMeasure μ] in
/-- The stochastic sum of the sum of two presentations is the sum of their stochastic sums. -/
theorem integral_add (d e : GridPresentation (κ := κ) μ T) :
    (d.add e).integral = d.integral + e.integral := by
  let rd := leftCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  let re := rightCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  have hp : (d.add e).integral = (d.pullback rd).integral + (e.pullback re).integral := by
    funext x
    simp only [integral, term, driverStep, add, rd, re, Pi.add_apply]
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  rw [hp, d.integral_pullback rd, e.integral_pullback re]

/-- The `L²` class of the stochastic sum is additive. -/
theorem integralLp_add (d e : GridPresentation (κ := κ) μ T) :
    (d.add e).integralLp = d.integralLp + e.integralLp := by
  apply Lp.ext
  filter_upwards [(d.add e).integralLp_coeFn,
    d.integralLp_coeFn, e.integralLp_coeFn,
    Lp.coeFn_add d.integralLp e.integralLp] with x ha hd he hs
  rw [ha, hs]
  simp only [Pi.add_apply]
  rw [hd, he]
  exact congrFun (d.integral_add e) x

/-- Scalar multiplication acts on every real noise coefficient. -/
def smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) : GridPresentation (κ := κ) μ T where
  steps := d.steps
  grid := d.grid
  initial_time := d.initial_time
  terminal_time := d.terminal_time
  coeff := fun k a x => c * d.coeff k a x
  adapted := fun k a => (d.adapted k a).const_mul c
  coeffL2 := fun k a => (d.coeffL2 k a).const_mul c

omit [IsProbabilityMeasure μ] in
theorem integral_smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) :
    (d.smul c).integral = c • d.integral := by
  funext x
  simp only [integral, term, driverStep, smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact (Finset.mul_sum Finset.univ _ _).symm

theorem integralLp_smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) :
    (d.smul c).integralLp = c • d.integralLp := by
  apply Lp.ext
  filter_upwards [(d.smul c).integralLp_coeFn,
    d.integralLp_coeFn, Lp.coeFn_smul c d.integralLp] with x ha hd hs
  rw [ha, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  exact congrFun (d.integral_smul c) x

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
