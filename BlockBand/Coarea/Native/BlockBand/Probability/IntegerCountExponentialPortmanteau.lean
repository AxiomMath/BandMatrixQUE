module

public import BlockBand.Coarea.Native.BlockBand.Probability.IntegerCountExponentialUI
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockCountConstruction

/-!
# Exponential moments pass to weak limits of integer count laws

The state space `ℕ` is discrete, so `k ↦ exp (t k)` is continuous.  The
open-set half of Portmanteau and the lower-semicontinuous integral inequality
therefore pass a uniform finite-volume exponential moment bound to a weak
limit.  Finiteness of the resulting lintegral gives Bochner
integrability of the limit observable.

This removes the limit-moment fields from the uniform-integrability hypothesis:
weak convergence plus the finite-volume exponential bounds suffice.  The
paper-facing constructor at the end fills
`PaperCountingLimitCompletionInput.countUI` automatically while retaining the
boundary, intensity-identification, close-pair, and mark-closure hypotheses
which do not follow from scalar count-law convergence.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology ENNReal

universe u

/-- Weak convergence and a uniform finite-volume exponential moment.  No
integrability or moment hypothesis is imposed separately on the limit law. -/
structure IntegerCountWeakExponentialInput
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

/-- Portmanteau passes the uniform exponential lintegral bound to the weak
limit. -/
theorem IntegerCountWeakExponentialInput.limit_lintegral_exp_le
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountWeakExponentialInput μs μ) :
    ∫⁻ k : ℕ, ENNReal.ofReal (Real.exp (input.exponent * k))
        ∂(μ : Measure ℕ) ≤ ENNReal.ofReal input.bound := by
  let f : ℕ → ℝ := fun k => Real.exp (input.exponent * k)
  have hcontinuous : Continuous f := continuous_of_discreteTopology
  have hnonneg : 0 ≤ f := fun k => (Real.exp_pos _).le
  have hopen : ∀ G : Set ℕ, IsOpen G →
      (μ : Measure ℕ) G ≤
        atTop.liminf (fun i => (μs i : Measure ℕ) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      input.law_tendsto hG
  have hport :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hcontinuous hnonneg hopen
  refine hport.trans ?_
  let I : ℕ → ENNReal := fun i =>
    ∫⁻ k : ℕ, ENNReal.ofReal (f k) ∂(μs i : Measure ℕ)
  have hbounded : IsBoundedUnder (fun x y : ENNReal => y ≤ x) atTop I :=
    ⟨0, by simp⟩
  apply liminf_le_of_le hbounded
  intro b hb
  obtain ⟨i, hi⟩ := hb.exists
  refine hi.trans ?_
  dsimp [I, f]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (input.approximating_exp_integrable i) (ae_of_all _ hnonneg)]
  exact ENNReal.ofReal_le_ofReal (input.approximating_exp_le i)

/-- The exponential observable is integrable under the weak limit. -/
theorem IntegerCountWeakExponentialInput.limit_exp_integrable
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountWeakExponentialInput μs μ) :
    Integrable (fun k : ℕ => Real.exp (input.exponent * k))
      (μ : Measure ℕ) := by
  let f : ℕ → ℝ := fun k => Real.exp (input.exponent * k)
  refine ⟨measurable_from_nat.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => (Real.exp_pos _).le)).2
  exact lt_of_le_of_lt input.limit_lintegral_exp_le ENNReal.ofReal_lt_top

/-- The real exponential moment of the weak limit obeys the same bound. -/
theorem IntegerCountWeakExponentialInput.limit_exp_le
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountWeakExponentialInput μs μ) :
    ∫ k : ℕ, Real.exp (input.exponent * k) ∂(μ : Measure ℕ) ≤ input.bound := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun k => (Real.exp_pos _).le)
    measurable_from_nat.aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    input.limit_lintegral_exp_le
  simpa [ENNReal.toReal_ofReal input.bound_nonneg] using h

/-- Portmanteau completes the full uniform-exponential input, including both
limit-law fields. -/
def IntegerCountWeakExponentialInput.toUniformExponentialInput
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountWeakExponentialInput μs μ) :
    IntegerCountUniformExponentialInput μs μ where
  law_tendsto := input.law_tendsto
  exponent := input.exponent
  exponent_pos := input.exponent_pos
  bound := input.bound
  bound_nonneg := input.bound_nonneg
  approximating_exp_integrable := input.approximating_exp_integrable
  approximating_exp_le := input.approximating_exp_le
  limit_exp_integrable := input.limit_exp_integrable
  limit_exp_le := input.limit_exp_le

/-- Weak convergence and uniform approximating exponential moments imply full
expectation convergence, with no separate limit-tail or limit-moment input. -/
def IntegerCountWeakExponentialInput.toExpectationConvergenceInput
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (input : IntegerCountWeakExponentialInput μs μ) :
    IntegerCountExpectationConvergenceInput μs μ :=
  input.toUniformExponentialInput.toExpectationConvergenceInput

/-- Measurability of the symmetric unfolded BlockGUE count. -/
theorem BlockGUE.measurable_unfoldedIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) :
    Measurable (BlockGUE.unfoldedIntervalCount M A₀ e L ρ R) := by
  unfold BlockGUE.unfoldedIntervalCount
  exact (measurable_eigenCount_Icc _ _).comp
    (measurable_blockGUE_deformed M A₀)

/-- The scalar natural-valued law of a normalized unfolded BlockGUE count. -/
def BlockGUE.unfoldedIntervalCountLaw
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) : ProbabilityMeasure ℕ :=
  naturalRandomVariableLaw M.P
    (BlockGUE.unfoldedIntervalCount M A₀ e L ρ R)
    (BlockGUE.measurable_unfoldedIntervalCount M A₀ e L ρ R)

/-- Every exponential observable of a normalized unfolded count law is
integrable, since the eigenvalue count is bounded by the matrix dimension. -/
theorem BlockGUE.integrable_exp_unfoldedIntervalCountLaw
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun n : ℕ => Real.exp (t * n))
      (BlockGUE.unfoldedIntervalCountLaw M A₀ e L ρ R : Measure ℕ) := by
  let count := BlockGUE.unfoldedIntervalCount M A₀ e L ρ R
  have hcount : Measurable count :=
    BlockGUE.measurable_unfoldedIntervalCount M A₀ e L ρ R
  have hunder : Integrable (fun ω => Real.exp (t * (count ω : ℝ))) M.P := by
    apply Integrable.of_bound
      ((Real.measurable_exp.comp
        (measurable_const.mul (measurable_from_nat.comp hcount))).aestronglyMeasurable)
      (Real.exp (t * (Fintype.card (BlockGUE.Index d) : ℝ)))
    filter_upwards with ω
    change |Real.exp (t * (count ω : ℝ))| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht
    have hnat := GaussianRing.eigenCount_le_dimension
      (BlockGUE.deformed M A₀ ω)
      (Set.Icc (e - R / (L * ρ)) (e + R / (L * ρ)))
    exact_mod_cast hnat
  change Integrable (fun n : ℕ => Real.exp (t * n)) (Measure.map count M.P)
  apply (integrable_map_measure
    ((Real.measurable_exp.comp
      (measurable_const.mul measurable_from_nat)).aestronglyMeasurable)
    hcount.aemeasurable).2
  simpa [Function.comp_def] using hunder

/-- The PSSS unfolded exponential estimate, expressed directly as a uniform
moment bound for the scalar count law used by Portmanteau. -/
theorem BlockGUE.integral_exp_unfoldedIntervalCountLaw_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hR : 0 ≤ R)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (ht : 0 ≤ t) :
    ∫ n : ℕ, Real.exp (t * n)
        ∂(BlockGUE.unfoldedIntervalCountLaw M A₀ e L ρ R : Measure ℕ) ≤
      Real.exp (2 * R * (input.C / ρ) * (Real.exp t - 1)) := by
  let count := BlockGUE.unfoldedIntervalCount M A₀ e L ρ R
  have hcount : Measurable count :=
    BlockGUE.measurable_unfoldedIntervalCount M A₀ e L ρ R
  unfold BlockGUE.unfoldedIntervalCountLaw
  change (∫ n : ℕ, Real.exp (t * n)
    ∂(naturalRandomVariableLaw M.P count hcount : Measure ℕ)) ≤ _
  rw [integral_naturalRandomVariableLaw M.P count hcount
    (fun n : ℕ => Real.exp (t * n))]
  · exact psss_unfoldedCountExponential input hd M A₀ e L ρ R t
      hL hρ hR hdim ht
  · exact Real.measurable_exp.comp (measurable_const.mul measurable_from_nat)

/-- Family-shaped weak convergence and finite-volume exponential bounds for
all scalar interval-count laws occurring in the paper completion. -/
structure PaperCountingWeakExponentialUIInput
    (countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ)
    (limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ) where
  weakExponential : ∀ n a b, a < b →
    IntegerCountWeakExponentialInput
      (fun i => countLaw i n a b) (limitCountLaw n a b)

/-- The scalar weak-convergence package automatically supplies all `countUI`
fields required by `paperCountingTheorem`. -/
def PaperCountingWeakExponentialUIInput.countUI
    {countLaw : ℕ → ℕ → ℝ → ℝ → ProbabilityMeasure ℕ}
    {limitCountLaw : ℕ → ℝ → ℝ → ProbabilityMeasure ℕ}
    (input : PaperCountingWeakExponentialUIInput countLaw limitCountLaw) :
    ∀ n a b, a < b →
      IntegerCountExpectationConvergenceInput
        (fun i => countLaw i n a b) (limitCountLaw n a b) :=
  fun n a b hab =>
    (input.weakExponential n a b hab).toExpectationConvergenceInput

/-- Constructor for the paper-facing limit completion in which the former
`countUI` obligation is replaced by scalar weak convergence and uniform
finite-volume exponential moments.  Physical count laws obtain the latter
from `GaussianRing.integral_exp_physicalUnfoldedCountLaw_le`; normalized PSSS
laws obtain them from the unfolded exponential estimate. -/
def paperCountingLimitCompletionInputOfWeakExponential
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState]
    (μ : ProbabilityMeasure VagueRationalWindowState) (φ : ℕ → ℕ)
    (boundaryClosure :
      BoundaryRegularLimitLawInput atTop (seq.vagueLaw ∘ φ) μ)
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
    (countExponential :
      PaperCountingWeakExponentialUIInput countLaw limitCountLaw)
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
        (limitIntensity n : Measure ℝ) {x})
    (windowRadius : ℕ → ℝ)
    (windowRadius_nonneg : ∀ j, 0 ≤ windowRadius j)
    (closePair : ℕ → ℝ → Set VagueRationalWindowState)
    (closePair_open : ∀ j a, 0 < a → IsOpen (closePair j a))
    (collision : ℕ → Set VagueRationalWindowState)
    (collision_subset_closePair : ∀ j a, 0 < a →
      collision j ⊆ closePair j a)
    (approximating_closePair_le : ∀ i j a, 0 < a →
      (seq.vagueLaw (φ i) : Measure VagueRationalWindowState) (closePair j a) ≤
        ENNReal.ofReal
          (8 * (input.C / seq.density_lower) ^ 2 * windowRadius j * a +
            16 * (input.C / seq.density_lower) ^ 2 * a ^ 2))
    (validMarks : Set VagueRationalWindowState)
    (validMarks_closed : IsClosed validMarks)
    (approximatingMarks_valid : ∀ i,
      (seq.vagueLaw (φ i) : Measure VagueRationalWindowState) validMarksᶜ = 0) :
    PaperCountingLimitCompletionInput input seq μ φ where
  boundaryClosure := boundaryClosure
  approximatingIntensity := approximatingIntensity
  limitIntensity := limitIntensity
  lipschitzConstant := lipschitzConstant
  lipschitzConstant_nonneg := lipschitzConstant_nonneg
  approximating_Icc_le := approximating_Icc_le
  countLaw := countLaw
  limitCountLaw := limitCountLaw
  countUI := countExponential.countUI
  approximating_expectation := approximating_expectation
  limit_expectation := limit_expectation
  singleton_expectation := singleton_expectation
  windowRadius := windowRadius
  windowRadius_nonneg := windowRadius_nonneg
  closePair := closePair
  closePair_open := closePair_open
  collision := collision
  collision_subset_closePair := collision_subset_closePair
  approximating_closePair_le := approximating_closePair_le
  validMarks := validMarks
  validMarks_closed := validMarks_closed
  approximatingMarks_valid := approximatingMarks_valid

end CoareaNative.BlockBand
