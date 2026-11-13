module

public import BlockBand.Coarea.Native.BlockBand.Counting.WeakLimitPointStateClosure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform integrability closes integer-count expectations

Weak convergence controls bounded continuous observables but does not by itself
control the expectation of an unbounded counting variable.  This module makes
the missing step explicit.  Natural-valued laws are tested against bounded
truncations `k ↦ min k R`; weak convergence gives convergence of every
truncated expectation, while a common vanishing truncation-error schedule
upgrades this to convergence of the full expectations.

The final constructor packages this result into
`CoordinateIntensityPassageInput`: once coordinate interval counts have the
specified laws and their expected counts equal the finite-volume and limiting
intensity masses, the previously explicit `Icc_tendsto` field is discharged.
No expectation convergence is inferred without the uniform tail hypotheses.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The bounded continuous truncation of the natural-valued count at level
`R`.  The domain `ℕ` is discrete and the range lies in `[0,R]`. -/
def truncatedNatCount (R : ℕ) : BoundedContinuousFunction ℕ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun k : ℕ => (min k R : ℝ)) (R : ℝ) (by
      intro k l
      rw [Real.dist_eq]
      have hk0 : 0 ≤ (min k R : ℝ) := by positivity
      have hl0 : 0 ≤ (min l R : ℝ) := by positivity
      have hkR : (min k R : ℝ) ≤ R := by exact_mod_cast min_le_right k R
      have hlR : (min l R : ℝ) ≤ R := by exact_mod_cast min_le_right l R
      exact abs_le.2 ⟨by linarith, by linarith⟩)

@[simp] theorem truncatedNatCount_apply (R k : ℕ) :
    truncatedNatCount R k = (min k R : ℝ) := rfl

/-- Expectation of the untruncated natural-valued count.  Integrability is not
built into this definition; it is required explicitly by the closure input. -/
def natCountExpectation (μ : ProbabilityMeasure ℕ) : ℝ :=
  ∫ k : ℕ, (k : ℝ) ∂(μ : Measure ℕ)

/-- Expectation of the bounded truncation. -/
def truncatedNatCountExpectation (μ : ProbabilityMeasure ℕ) (R : ℕ) : ℝ :=
  ∫ k : ℕ, truncatedNatCount R k ∂(μ : Measure ℕ)

/-- Expected excess above the bounded truncation.  For a count `k` this
is `k - min k R`, the standard uniform-integrability tail observable. -/
def natCountTailExpectation (μ : ProbabilityMeasure ℕ) (R : ℕ) : ℝ :=
  ∫ k : ℕ, ((k : ℝ) - (min k R : ℝ)) ∂(μ : Measure ℕ)

/-- Bounded count truncations are integrable under every probability law. -/
theorem integrable_truncatedNatCount (μ : ProbabilityMeasure ℕ) (R : ℕ) :
    Integrable (fun k => truncatedNatCount R k) (μ : Measure ℕ) := by
  refine Integrable.of_bound
    (truncatedNatCount R).continuous.aestronglyMeasurable (R : ℝ)
    (ae_of_all _ fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · simp only [truncatedNatCount_apply]
    exact_mod_cast min_le_right k R
  · simp only [truncatedNatCount_apply]
    positivity

/-- The truncation error in the expectation is exactly the expected tail. -/
theorem dist_natCountExpectation_truncated_eq_tail
    (μ : ProbabilityMeasure ℕ) (R : ℕ)
    (hint : Integrable (fun k : ℕ => (k : ℝ)) (μ : Measure ℕ)) :
    dist (natCountExpectation μ) (truncatedNatCountExpectation μ R) =
      natCountTailExpectation μ R := by
  rw [natCountExpectation, truncatedNatCountExpectation, Real.dist_eq,
    ← integral_sub hint (integrable_truncatedNatCount μ R)]
  unfold natCountTailExpectation
  have hnonneg : 0 ≤ ∫ k : ℕ,
      ((k : ℝ) - truncatedNatCount R k) ∂(μ : Measure ℕ) := by
    apply integral_nonneg
    intro k
    simp only [truncatedNatCount_apply]
    exact sub_nonneg.mpr (by exact_mod_cast min_le_left k R)
  rw [abs_of_nonneg hnonneg]
  apply integral_congr_ae
  filter_upwards with k
  simp only [truncatedNatCount_apply]

/-- Exact uniform-integrability input for a weakly convergent sequence of
integer-count laws.

The two error fields are the usual uniform-tail assertion, written in the
precise form used by the proof.  In applications they follow from bounds on
`E[k 1_{k>R}]`.  The limit-law error is retained explicitly rather than being
silently deduced from weak convergence. -/
structure IntegerCountExpectationConvergenceInput
    (μs : ℕ → ProbabilityMeasure ℕ) (μ : ProbabilityMeasure ℕ) where
  law_tendsto : Tendsto μs atTop (𝓝 μ)
  approximating_integrable :
    ∀ i, Integrable (fun k : ℕ => (k : ℝ)) (μs i : Measure ℕ)
  limit_integrable : Integrable (fun k : ℕ => (k : ℝ)) (μ : Measure ℕ)
  tailBound : ℕ → ℝ
  tailBound_nonneg : ∀ R, 0 ≤ tailBound R
  tailBound_tendsto_zero : Tendsto tailBound atTop (𝓝 0)
  approximating_truncation_error :
    ∀ i R,
      dist (natCountExpectation (μs i))
        (truncatedNatCountExpectation (μs i) R) ≤ tailBound R
  limit_truncation_error :
    ∀ R,
      dist (truncatedNatCountExpectation μ R)
        (natCountExpectation μ) ≤ tailBound R

/-- Conventional uniform-tail formulation.  Both the approximating
laws and the limit law have expected excess above `min(k,R)` bounded by the
same deterministic schedule tending to zero. -/
structure IntegerCountUniformTailInput
    (μs : ℕ → ProbabilityMeasure ℕ) (μ : ProbabilityMeasure ℕ) where
  law_tendsto : Tendsto μs atTop (𝓝 μ)
  approximating_integrable :
    ∀ i, Integrable (fun k : ℕ => (k : ℝ)) (μs i : Measure ℕ)
  limit_integrable : Integrable (fun k : ℕ => (k : ℝ)) (μ : Measure ℕ)
  tailBound : ℕ → ℝ
  tailBound_nonneg : ∀ R, 0 ≤ tailBound R
  tailBound_tendsto_zero : Tendsto tailBound atTop (𝓝 0)
  approximating_tail_le :
    ∀ i R, natCountTailExpectation (μs i) R ≤ tailBound R
  limit_tail_le : ∀ R, natCountTailExpectation μ R ≤ tailBound R

/-- Conventional expected-tail bounds give the truncation-error package. -/
def IntegerCountUniformTailInput.toExpectationConvergenceInput
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformTailInput μs μ) :
    IntegerCountExpectationConvergenceInput μs μ where
  law_tendsto := input.law_tendsto
  approximating_integrable := input.approximating_integrable
  limit_integrable := input.limit_integrable
  tailBound := input.tailBound
  tailBound_nonneg := input.tailBound_nonneg
  tailBound_tendsto_zero := input.tailBound_tendsto_zero
  approximating_truncation_error i R := by
    rw [dist_natCountExpectation_truncated_eq_tail
      (μs i) R (input.approximating_integrable i)]
    exact input.approximating_tail_le i R
  limit_truncation_error R := by
    rw [dist_comm, dist_natCountExpectation_truncated_eq_tail
      μ R input.limit_integrable]
    exact input.limit_tail_le R

/-- Weak convergence gives convergence of every bounded truncated count
expectation. -/
theorem IntegerCountExpectationConvergenceInput.truncated_tendsto
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountExpectationConvergenceInput μs μ) (R : ℕ) :
    Tendsto (fun i => truncatedNatCountExpectation (μs i) R) atTop
      (𝓝 (truncatedNatCountExpectation μ R)) := by
  simpa [truncatedNatCountExpectation] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      input.law_tendsto (truncatedNatCount R))

/-- **Uniform-integrability closure for integer counts.**  Weak convergence of
the count laws together with a common vanishing truncation-error schedule
implies convergence of their full expectations. -/
theorem IntegerCountExpectationConvergenceInput.expectation_tendsto
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountExpectationConvergenceInput μs μ) :
    Tendsto (fun i => natCountExpectation (μs i)) atTop
      (𝓝 (natCountExpectation μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevTail : ∀ᶠ R in atTop, input.tailBound R < ε / 3 :=
    (tendsto_order.1 input.tailBound_tendsto_zero).2 _ (by linarith)
  obtain ⟨R, hR⟩ := hevTail.exists
  have htrunc := (input.truncated_tendsto R)
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 htrunc) (ε / 3) (by linarith)
  refine ⟨N, fun i hiN => ?_⟩
  have hi := hN i hiN
  calc
    dist (natCountExpectation (μs i)) (natCountExpectation μ) ≤
        dist (natCountExpectation (μs i))
            (truncatedNatCountExpectation (μs i) R) +
          dist (truncatedNatCountExpectation (μs i) R)
            (truncatedNatCountExpectation μ R) +
          dist (truncatedNatCountExpectation μ R)
            (natCountExpectation μ) := by
      exact (dist_triangle4 _ _ _ _)
    _ ≤ input.tailBound R +
          dist (truncatedNatCountExpectation (μs i) R)
            (truncatedNatCountExpectation μ R) + input.tailBound R := by
      gcongr
      · exact input.approximating_truncation_error i R
      · exact input.limit_truncation_error R
    _ < ε := by linarith

/-- Weak convergence plus the conventional uniform-tail hypothesis
implies convergence of full integer-count expectations. -/
theorem IntegerCountUniformTailInput.expectation_tendsto
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformTailInput μs μ) :
    Tendsto (fun i => natCountExpectation (μs i)) atTop
      (𝓝 (natCountExpectation μ)) :=
  input.toExpectationConvergenceInput.expectation_tendsto

/-- Nonnegativity of natural-count expectations. -/
theorem natCountExpectation_nonneg (μ : ProbabilityMeasure ℕ) :
    0 ≤ natCountExpectation μ := by
  exact integral_nonneg fun k => Nat.cast_nonneg k

/-- Build the interval-intensity passage package from integer-valued
count laws satisfying weak convergence and uniform integrability.

The two expectation identities fix all normalizations: finite and limiting
`Icc` masses are `ofReal` of the corresponding integer-count expectations. -/
def coordinateIntensityPassageInputOfIntegerCountUI
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (approximatingIntensity : ℕ → ℕ → FiniteMeasure ℝ)
    (limitIntensity : ℕ → FiniteMeasure ℝ)
    (lipschitzConstant : ℕ → ℝ)
    (lipschitzConstant_nonneg : ∀ n, 0 ≤ lipschitzConstant n)
    (approximating_Icc_le :
      ∀ i n a b, a < b →
        (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) ≤
          ENNReal.ofReal (lipschitzConstant n * (b - a)))
    (countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ)
    (limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ)
    (countUI : ∀ n a b, a < b →
      IntegerCountExpectationConvergenceInput
        (fun i => countLaw i n a b) (limitCountLaw n a b))
    (approximating_expectation :
      ∀ i n a b, a < b →
        (approximatingIntensity i n : Measure ℝ) (Set.Icc a b) =
          ENNReal.ofReal (natCountExpectation (countLaw i n a b)))
    (limit_expectation :
      ∀ n a b, a < b →
        (limitIntensity n : Measure ℝ) (Set.Icc a b) =
          ENNReal.ofReal (natCountExpectation (limitCountLaw n a b)))
    (singleton_expectation :
      ∀ n x,
        ∫⁻ ν, (ν n : Measure (MarkedSpectralSpace Unit))
            (spectralEndpointFiber x)
          ∂(μ : Measure VagueRationalWindowState) =
        (limitIntensity n : Measure ℝ) {x}) :
    CoordinateIntensityPassageInput μ where
  approximatingIntensity := approximatingIntensity
  limitIntensity := limitIntensity
  lipschitzConstant := lipschitzConstant
  lipschitzConstant_nonneg := lipschitzConstant_nonneg
  approximating_Icc_le := approximating_Icc_le
  Icc_tendsto n a b hab := by
    have hreal := (countUI n a b hab).expectation_tendsto
    have henn : Tendsto
        (fun i => ENNReal.ofReal
          (natCountExpectation (countLaw i n a b))) atTop
        (𝓝 (ENNReal.ofReal
          (natCountExpectation (limitCountLaw n a b)))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [← approximating_expectation _ n a b hab,
      ← limit_expectation n a b hab] using henn
  singleton_expectation := singleton_expectation

end CoareaNative.BlockBand
