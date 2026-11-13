module

public import Mathlib

/-!
# Exact finite close-pair covering

A set of ordered distinct pairs covered by finitely many windows has cardinality at most
the sum of the second descending factorials of the window counts; taking expectations,
second factorial moment bounds for the windows bound the expected close-pair count.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Counting

open MeasureTheory
open scoped BigOperators

universe u v w

/-- Ordered distinct pairs drawn from a finite set. -/
def orderedDistinctPairs {ι : Type u} [DecidableEq ι]
    (s : Finset ι) : Finset (ι × ι) :=
  s.offDiag

/-- The ordered distinct-pair count is the second descending factorial. -/
theorem card_orderedDistinctPairs_eq_descFactorial
    {ι : Type u} [DecidableEq ι] (s : Finset ι) :
    (orderedDistinctPairs s).card = s.card.descFactorial 2 := by
  rw [orderedDistinctPairs, Finset.offDiag_card]
  generalize s.card = n
  cases n <;> simp [Nat.descFactorial, Nat.succ_mul, Nat.mul_succ]

/-- Deterministic covering lemma behind the close-pair estimate.
Every counted ordered pair may occur in more than one enlarged window; only
coverage, not disjointness, is required. -/
theorem card_pairs_le_sum_descFactorial_of_subset_biUnion
    {ι : Type u} {κ : Type v} [DecidableEq ι] [DecidableEq κ]
    (pairs : Finset (ι × ι)) (bins : Finset κ)
    (window : κ → Finset ι)
    (hcover : pairs ⊆ bins.biUnion fun b => orderedDistinctPairs (window b)) :
    pairs.card ≤
      ∑ b ∈ bins, (window b).card.descFactorial 2 := by
  calc
    pairs.card ≤ (bins.biUnion fun b =>
        orderedDistinctPairs (window b)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ b ∈ bins, (orderedDistinctPairs (window b)).card :=
      Finset.card_biUnion_le
    _ = ∑ b ∈ bins, (window b).card.descFactorial 2 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact card_orderedDistinctPairs_eq_descFactorial (window b)

/-- Expectation form of the finite covering argument.  After the geometric line covering, a pointwise
cover by windows plus a second-factorial-moment estimate for each window
bounds the expected ordered close-pair count by the sum of the window
constants. -/
theorem integral_pairCount_le_sum_sq_of_factorialMoments
    {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω)
    {κ : Type v} [DecidableEq κ] (bins : Finset κ)
    (pairCount : Ω → ℕ) (windowCount : κ → Ω → ℕ)
    (q : κ → ℝ)
    (hpairInt : Integrable (fun ω => (pairCount ω : ℝ)) μ)
    (hwindowInt : ∀ b ∈ bins,
      Integrable (fun ω => ((windowCount b ω).descFactorial 2 : ℝ)) μ)
    (hcover : ∀ ω, pairCount ω ≤
      ∑ b ∈ bins, (windowCount b ω).descFactorial 2)
    (hmoment : ∀ b ∈ bins,
      ∫ ω, ((windowCount b ω).descFactorial 2 : ℝ) ∂μ ≤ (q b) ^ 2) :
    ∫ ω, (pairCount ω : ℝ) ∂μ ≤ ∑ b ∈ bins, (q b) ^ 2 := by
  calc
    (∫ ω, (pairCount ω : ℝ) ∂μ) ≤
        ∫ ω, ∑ b ∈ bins,
          ((windowCount b ω).descFactorial 2 : ℝ) ∂μ := by
      apply integral_mono hpairInt
      · exact integrable_finsetSum bins fun b hb => hwindowInt b hb
      · intro ω
        calc
          (pairCount ω : ℝ) ≤
              (∑ b ∈ bins, (windowCount b ω).descFactorial 2 : ℕ) := by
            exact_mod_cast hcover ω
          _ = ∑ b ∈ bins,
              ((windowCount b ω).descFactorial 2 : ℝ) := by
            simp only [Nat.cast_sum]
    _ = ∑ b ∈ bins,
        ∫ ω, ((windowCount b ω).descFactorial 2 : ℝ) ∂μ := by
      rw [integral_finsetSum]
      intro b hb
      exact hwindowInt b hb
    _ ≤ ∑ b ∈ bins, (q b) ^ 2 := by
      exact Finset.sum_le_sum fun b hb => hmoment b hb

end BlockBand.Counting
