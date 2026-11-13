module

public import BlockBand.External.PSSS.Statement

/-!
# Elementary properties of factorial moments of counts

For a finite measure and a measurable natural-valued count bounded by a dimension, this file
proves that the falling-factorial counts are measurable, bounded and integrable, that the
factorial-moment bound transfers between identically distributed counts, and an induction
principle (`exists_uniform_allOrder_of_base_successor`) giving one constant valid for all orders
from a base case and an order-independent induction step.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.External.PSSS

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The falling factorial count equals the real product `∏_{j<r} (count - j)`, also when
`r > count` (both sides then vanish). -/
theorem factorialCount_eq_prod_sub {Ω : Type*} (count : Ω → ℕ)
    (r : ℕ) (ω : Ω) :
    factorialCount count r ω =
      ∏ j ∈ Finset.range r, ((count ω : ℝ) - (j : ℝ)) := by
  change ((count ω).descFactorial r : ℝ) = _
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ, ← ih]
      have hrec :
          ((count ω).descFactorial r : ℝ) * (count ω : ℝ) =
            ((count ω).descFactorial (r + 1) : ℝ) +
              (r : ℝ) * ((count ω).descFactorial r : ℝ) := by
        exact_mod_cast Nat.descFactorial_mul_self (count ω) r
      nlinarith

/-- A measurable count has measurable falling-factorial counts at every order. -/
theorem measurable_factorialCount {Ω : Type*} [MeasurableSpace Ω]
    {count : Ω → ℕ} (hcount : Measurable count) (r : ℕ) :
    Measurable (factorialCount count r) := by
  have hfactorial : Measurable (fun n : ℕ => (n.descFactorial r : ℝ)) :=
    measurable_from_nat
  exact hfactorial.comp hcount

/-- If `count ≤ dimension`, then the falling-factorial count of order `r` is at most
`dimension^r`. -/
theorem factorialCount_le_dimension_pow {Ω : Type*} {count : Ω → ℕ}
    {dimension : ℕ} (hbound : ∀ ω, count ω ≤ dimension) (r : ℕ) (ω : Ω) :
    factorialCount count r ω ≤ (dimension : ℝ) ^ r := by
  simpa only [factorialCount, Nat.cast_pow] using
    (Nat.cast_le.mpr ((Nat.descFactorial_le_pow (count ω) r).trans
      (Nat.pow_le_pow_left (hbound ω) r)) :
        ((count ω).descFactorial r : ℝ) ≤ (dimension ^ r : ℕ))

/-- Under a finite measure, a bounded measurable count has integrable falling-factorial counts
at every order. -/
theorem integrable_factorialCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {count : Ω → ℕ}
    (hcount : Measurable count) {dimension : ℕ}
    (hbound : ∀ ω, count ω ≤ dimension) (r : ℕ) :
    Integrable (factorialCount count r) μ := by
  apply Integrable.of_bound
    (measurable_factorialCount hcount r).aestronglyMeasurable
    ((dimension : ℝ) ^ r)
  filter_upwards with ω
  change ‖((count ω).descFactorial r : ℝ)‖ ≤ (dimension : ℝ) ^ r
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact factorialCount_le_dimension_pow hbound r ω

/-- Identically distributed counts have equal factorial moments at every order. -/
theorem factorialCount_integral_eq_of_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {count : Ω → ℕ} {count' : Ω' → ℕ}
    (hlaw : IdentDistrib count count' μ ν) (r : ℕ) :
    (∫ ω, factorialCount count r ω ∂μ) =
      ∫ ω, factorialCount count' r ω ∂ν := by
  have hfactorial : Measurable (fun n : ℕ => (n.descFactorial r : ℝ)) :=
    measurable_from_nat
  exact (hlaw.comp hfactorial).integral_eq

/-- Exact-law transport keeps the same constant, dimension, interval length and
factorial order.
The adapter must supply `IdentDistrib` for the counts;
no equality between a physical characteristic-function law and the normalized block-product law is asserted by this generic result.
-/
theorem factorialMomentBound_transport
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {count : Ω → ℕ} {count' : Ω' → ℕ}
    (hlaw : IdentDistrib count count' μ ν)
    {dimension : ℕ} {intervalLength C : ℝ} {r : ℕ}
    (hbound : FactorialMomentBound ν count' dimension intervalLength C r) :
    FactorialMomentBound μ count dimension intervalLength C r := by
  unfold FactorialMomentBound at hbound ⊢
  rw [factorialCount_integral_eq_of_identDistrib hlaw r]
  exact hbound

/-- The factorial-moment bound persists when the nonnegative constant `C` is enlarged, for a
nonnegative interval length. -/
theorem factorialMomentBound_mono_constant
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {count : Ω → ℕ}
    {dimension : ℕ} {intervalLength C C' : ℝ} {r : ℕ}
    (hC : 0 ≤ C) (hlen : 0 ≤ intervalLength) (hCC' : C ≤ C')
    (hbound : FactorialMomentBound μ count dimension intervalLength C r) :
    FactorialMomentBound μ count dimension intervalLength C' r := by
  unfold FactorialMomentBound at hbound ⊢
  refine hbound.trans ?_
  gcongr

/-- Induction on the order with a uniform constant: if `P C 1` holds for some `C ≥ 1` and is
monotone in `C`, and there is `K ≥ 1` such that `P C r → P C (r + 1)` for all `C ≥ K` and all
`r`, then a single `C ≥ 1` satisfies `P C r` for every `r ≥ 1`. Any uniformity in dimensions,
deformations or intervals must be built into `P`. -/
theorem exists_uniform_allOrder_of_base_successor (P : ℝ → ℕ → Prop)
    (hbase : ∃ C : ℝ, 1 ≤ C ∧ P C 1)
    (hbase_mono : ∀ C C' : ℝ, C ≤ C' → P C 1 → P C' 1)
    (hsuccessor : ∃ K : ℝ, 1 ≤ K ∧
      ∀ C : ℝ, K ≤ C → ∀ r : ℕ, P C r → P C (r + 1)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → P C r := by
  obtain ⟨K, hK, hstep⟩ := hsuccessor
  obtain ⟨CW, _, hW⟩ := hbase
  let C := max K CW
  have hKC : K ≤ C := le_max_left _ _
  have hC : 1 ≤ C := hK.trans hKC
  have hfirst : P C 1 := hbase_mono CW C (le_max_right _ _) hW
  refine ⟨C, hC, ?_⟩
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
      cases r with
      | zero => simpa using hfirst
      | succ r => exact hstep C hKC (r + 1) (ih (by omega))

end BlockBand.External.PSSS
