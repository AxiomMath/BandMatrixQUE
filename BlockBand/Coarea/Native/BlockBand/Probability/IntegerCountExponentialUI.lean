module

public import BlockBand.Coarea.Native.BlockBand.Counting.PaperCountingTheorem
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Uniform integrability of integer counts from exponential moments

A positive exponential moment controls the unbounded integer count uniformly.
The proof uses the explicit tail comparison

`k - min k R ≤ exp (-t R) / t * exp (t k)`.

Thus a common exponential-moment bound gives a deterministic tail schedule
which tends to zero.  This supplies the uniform-integrability field of
`PaperCountingLimitCompletionInput`.  The final declarations also turn a
physical unfolded count into a probability law and transport the
physical exponential estimate to that law.  Weak convergence of those
laws is a hypothesis: no convergence is inferred from moment
bounds alone.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

universe u

/-- A natural count is dominated by its positive exponential moment. -/
theorem natCast_le_exp_mul_div (t : ℝ) (ht : 0 < t) (k : ℕ) :
    (k : ℝ) ≤ Real.exp (t * k) / t := by
  rw [le_div_iff₀ ht]
  have h := Real.add_one_le_exp (t * (k : ℝ))
  nlinarith

/-- The excess over truncation level `R` has an exponentially decaying
pointwise majorant. -/
theorem natCountTail_le_exp_majorant (t : ℝ) (ht : 0 < t) (R k : ℕ) :
    (k : ℝ) - (min k R : ℝ) ≤
      (Real.exp (-(t * R)) / t) * Real.exp (t * k) := by
  by_cases hk : k ≤ R
  · rw [min_eq_left (by exact_mod_cast hk)]
    simp only [sub_self]
    positivity
  · have hRk : R ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    rw [min_eq_right (by exact_mod_cast hRk)]
    have hbase := Real.add_one_le_exp (t * ((k - R : ℕ) : ℝ))
    have hbound : ((k - R : ℕ) : ℝ) ≤
        Real.exp (t * ((k - R : ℕ) : ℝ)) / t := by
      rw [le_div_iff₀ ht]
      nlinarith
    rw [Nat.cast_sub hRk] at hbound
    calc
      (k : ℝ) - (R : ℝ) ≤
          Real.exp (t * ((k : ℝ) - (R : ℝ))) / t := hbound
      _ = (Real.exp (-(t * R)) / t) * Real.exp (t * k) := by
        have hexpid : Real.exp (t * ((k : ℝ) - (R : ℝ))) =
            Real.exp (-(t * R)) * Real.exp (t * k) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexpid]
        ring

/-- Exponential integrability implies integrability of the natural count. -/
theorem integrable_natCast_of_exp
    (μ : ProbabilityMeasure ℕ) (t : ℝ) (ht : 0 < t)
    (hexp : Integrable (fun k : ℕ => Real.exp (t * k)) (μ : Measure ℕ)) :
    Integrable (fun k : ℕ => (k : ℝ)) (μ : Measure ℕ) := by
  apply Integrable.mono'
    (hexp.const_mul (1 / t))
    (measurable_from_nat.aestronglyMeasurable)
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  simpa [one_div, div_eq_mul_inv, mul_comm] using natCast_le_exp_mul_div t ht k

/-- The expected truncation excess is controlled by the exponential moment. -/
theorem natCountTailExpectation_le_of_exp
    (μ : ProbabilityMeasure ℕ) (t B : ℝ) (ht : 0 < t)
    (hexp : Integrable (fun k : ℕ => Real.exp (t * k)) (μ : Measure ℕ))
    (hexp_le : ∫ k : ℕ, Real.exp (t * k) ∂(μ : Measure ℕ) ≤ B)
    (R : ℕ) :
    natCountTailExpectation μ R ≤ Real.exp (-(t * R)) / t * B := by
  have htailint : Integrable
      (fun k : ℕ => (k : ℝ) - (min k R : ℝ)) (μ : Measure ℕ) :=
    (integrable_natCast_of_exp μ t ht hexp).sub
      (integrable_truncatedNatCount μ R)
  have hmajorint : Integrable
      (fun k : ℕ => (Real.exp (-(t * R)) / t) * Real.exp (t * k))
      (μ : Measure ℕ) := hexp.const_mul _
  unfold natCountTailExpectation
  calc
    (∫ k : ℕ, ((k : ℝ) - (min k R : ℝ)) ∂(μ : Measure ℕ)) ≤
        ∫ k : ℕ, (Real.exp (-(t * R)) / t) * Real.exp (t * k)
          ∂(μ : Measure ℕ) := by
      apply integral_mono htailint hmajorint
      intro k
      exact natCountTail_le_exp_majorant t ht R k
    _ = (Real.exp (-(t * R)) / t) *
        ∫ k : ℕ, Real.exp (t * k) ∂(μ : Measure ℕ) := by
      rw [integral_const_mul]
    _ ≤ (Real.exp (-(t * R)) / t) * B := by
      gcongr

/-- A common positive exponential moment for approximating and limiting count
laws.  Weak convergence is kept separate and explicit. -/
structure IntegerCountUniformExponentialInput
    (μs : ℕ → ProbabilityMeasure ℕ) (μ : ProbabilityMeasure ℕ) where
  law_tendsto : Tendsto μs atTop (𝓝 μ)
  exponent : ℝ
  exponent_pos : 0 < exponent
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  approximating_exp_integrable : ∀ i,
    Integrable (fun k : ℕ => Real.exp (exponent * k)) (μs i : Measure ℕ)
  approximating_exp_le : ∀ i,
    ∫ k : ℕ, Real.exp (exponent * k) ∂(μs i : Measure ℕ) ≤ bound
  limit_exp_integrable :
    Integrable (fun k : ℕ => Real.exp (exponent * k)) (μ : Measure ℕ)
  limit_exp_le :
    ∫ k : ℕ, Real.exp (exponent * k) ∂(μ : Measure ℕ) ≤ bound

/-- The explicit exponentially decaying tail schedule. -/
def IntegerCountUniformExponentialInput.tailBound
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformExponentialInput μs μ) (R : ℕ) : ℝ :=
  Real.exp (-(input.exponent * R)) / input.exponent * input.bound

/-- The exponential tail schedule tends to zero. -/
theorem IntegerCountUniformExponentialInput.tailBound_tendsto_zero
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformExponentialInput μs μ) :
    Tendsto input.tailBound atTop (𝓝 0) := by
  have hscale : Tendsto (fun R : ℕ => input.exponent * (R : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop input.exponent_pos)
  have hexp : Tendsto (fun R : ℕ => Real.exp (-(input.exponent * R)))
      atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).congr' ?_
    filter_upwards with R
    rfl
  change Tendsto (fun R : ℕ =>
    Real.exp (-(input.exponent * (R : ℝ))) / input.exponent * input.bound)
    atTop (𝓝 0)
  simpa only [zero_div, zero_mul] using
    (hexp.div_const input.exponent).mul_const input.bound

/-- Uniform exponential moments automatically provide the conventional
uniform-integrability tail input. -/
def IntegerCountUniformExponentialInput.toUniformTailInput
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformExponentialInput μs μ) :
    IntegerCountUniformTailInput μs μ where
  law_tendsto := input.law_tendsto
  approximating_integrable i := integrable_natCast_of_exp
    (μs i) input.exponent input.exponent_pos
    (input.approximating_exp_integrable i)
  limit_integrable := integrable_natCast_of_exp μ input.exponent
    input.exponent_pos input.limit_exp_integrable
  tailBound := input.tailBound
  tailBound_nonneg R := by
    unfold IntegerCountUniformExponentialInput.tailBound
    exact mul_nonneg (div_nonneg (Real.exp_nonneg _) input.exponent_pos.le)
      input.bound_nonneg
  tailBound_tendsto_zero := input.tailBound_tendsto_zero
  approximating_tail_le i R := by
    exact natCountTailExpectation_le_of_exp
      (μs i) input.exponent input.bound input.exponent_pos
      (input.approximating_exp_integrable i) (input.approximating_exp_le i) R
  limit_tail_le R := by
    exact natCountTailExpectation_le_of_exp
      μ input.exponent input.bound input.exponent_pos
      input.limit_exp_integrable input.limit_exp_le R

/-- The expectation-convergence package required by the paper counting theorem
is therefore automatic from weak convergence and the common exponential
moment. -/
def IntegerCountUniformExponentialInput.toExpectationConvergenceInput
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountUniformExponentialInput μs μ) :
    IntegerCountExpectationConvergenceInput μs μ :=
  input.toUniformTailInput.toExpectationConvergenceInput

/-- Regard a measurable natural-valued random variable on a probability space
as its probability law. -/
def naturalRandomVariableLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (_hN : Measurable N) : ProbabilityMeasure ℕ :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) N

/-- Integration against a natural-valued pushforward law. -/
theorem integral_naturalRandomVariableLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (f : ℕ → ℝ) (hf : Measurable f) :
    ∫ k, f k ∂(naturalRandomVariableLaw μ N hN : Measure ℕ) =
      ∫ ω, f (N ω) ∂μ := by
  change ∫ k, f k ∂Measure.map N μ = _
  exact integral_map hN.aemeasurable hf.aestronglyMeasurable

/-- The physical unfolded count law attached to a multi-block transport. -/
def GaussianRing.physicalUnfoldedCountLaw
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    (p : Params)
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (_transport : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    (hmeas : ∀ a b, Measurable (N a b))
    (e L ρ R : ℝ) : ProbabilityMeasure ℕ :=
  naturalRandomVariableLaw μ
    (transportedUnfoldedIntervalCount N e L ρ R)
    (hmeas (e - R / (L * ρ)) (e + R / (L * ρ)))

/-- The exponential observable is integrable under a physical unfolded count
law.  This uses only the deterministic matrix-dimension bound in the joint
transport. -/
theorem GaussianRing.integrable_exp_physicalUnfoldedCountLaw
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    (p : Params)
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (transport : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    (hmeas : ∀ a b, Measurable (N a b))
    (e L ρ R t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun k : ℕ => Real.exp (t * k))
      (physicalUnfoldedCountLaw μ ν p G A₀ N transport hmeas e L ρ R :
        Measure ℕ) := by
  let a := e - R / (L * ρ)
  let b := e + R / (L * ρ)
  let count : Ω → ℕ := N a b
  have hcount : Measurable count := hmeas a b
  have hunder : Integrable (fun ω => Real.exp (t * (count ω : ℝ))) μ := by
    apply Integrable.of_bound
      ((Real.measurable_exp.comp
        (measurable_const.mul (measurable_from_nat.comp hcount))).aestronglyMeasurable)
      (Real.exp (t * (p.n * p.W : ℝ)))
    filter_upwards with ω
    change |Real.exp (t * (count ω : ℝ))| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast transport.count_le_dimension a b ω) ht
  change Integrable (fun k : ℕ => Real.exp (t * k)) (Measure.map count μ)
  apply (integrable_map_measure
    ((Real.measurable_exp.comp
      (measurable_const.mul measurable_from_nat)).aestronglyMeasurable)
    hcount.aemeasurable).2
  simpa [Function.comp_def] using hunder

/-- The physical unfolded exponential estimate is exactly the exponential
moment bound of its natural-valued count law. -/
theorem GaussianRing.integral_exp_physicalUnfoldedCountLaw_le
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (input : PSSSInput.{u})
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : Params)
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (transport : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    (hmeas : ∀ a b, Measurable (N a b))
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hdim : (p.n * p.W : ℝ) ≤ L) (ht : 0 ≤ t) :
    ∫ k : ℕ, Real.exp (t * k)
        ∂(physicalUnfoldedCountLaw μ ν p G A₀ N transport hmeas e L ρ R :
          Measure ℕ) ≤
      Real.exp (2 * R * ((input.C / Real.sqrt p.c) / ρ) *
        (Real.exp t - 1)) := by
  let count := transportedUnfoldedIntervalCount N e L ρ R
  have hcount : Measurable count :=
    hmeas (e - R / (L * ρ)) (e + R / (L * ρ))
  unfold physicalUnfoldedCountLaw
  change (∫ k : ℕ, Real.exp (t * k)
    ∂(naturalRandomVariableLaw μ count hcount : Measure ℕ)) ≤ _
  rw [integral_naturalRandomVariableLaw μ count hcount
    (fun k : ℕ => Real.exp (t * k))]
  · exact transport.unfoldedCountExponential input μ ν G A₀ N
      e L ρ R t hL hρ hR hdim ht
  · exact Real.measurable_exp.comp (measurable_const.mul measurable_from_nat)

/-- Exponential-moment data in exactly the family shape required by the
`countUI` field of `PaperCountingLimitCompletionInput`. -/
structure PaperCountingExponentialUIInput
    (countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ)
    (limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ) where
  uniformExponential : ∀ n a b, a < b →
    IntegerCountUniformExponentialInput
      (fun i => countLaw i n a b) (limitCountLaw n a b)

/-- Uniform exponential moments discharge every integer-count expectation
convergence obligation in the paper-facing completion input. -/
def PaperCountingExponentialUIInput.countUI
    {countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ}
    {limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ}
    (input : PaperCountingExponentialUIInput countLaw limitCountLaw) :
    ∀ n a b, a < b →
      IntegerCountExpectationConvergenceInput
        (fun i => countLaw i n a b) (limitCountLaw n a b) :=
  fun n a b hab =>
    (input.uniformExponential n a b hab).toExpectationConvergenceInput

end CoareaNative.BlockBand
