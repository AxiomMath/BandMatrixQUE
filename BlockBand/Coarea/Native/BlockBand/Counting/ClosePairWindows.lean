module

public import BlockBand.Coarea.Native.BlockBand.Counting.ClosePairs
public import BlockBand.Coarea.Native.BlockBand.Counting.Factorial

/-!
# PSSS estimate for a finite close-pair window cover

This module instantiates the abstract close-pair covering inequality with the
PSSS second factorial moment.  The result accepts explicit physical interval
endpoints; the remaining line-grid lemma only has to prove the pointwise cover
and bound the number and width of those intervals.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators

universe u v

/-- Expected ordered-pair bound for an explicit finite family of covering
intervals.  The pair count itself is kept abstract so that the same theorem
can be reused for unfolded eigenvalues and for marked spectral locations. -/
theorem psss_pairCount_le_sum_windowSquares
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    {κ : Type v} [DecidableEq κ] (bins : Finset κ)
    (lo hi : κ → ℝ) (hlohi : ∀ b ∈ bins, lo b ≤ hi b)
    (pairCount : M.Ω → ℕ)
    (hpairInt : Integrable (fun ω => (pairCount ω : ℝ)) M.P)
    (hcover : ∀ ω, pairCount ω ≤
      ∑ b ∈ bins,
        (BlockGUE.intervalCount M A₀ (Set.Icc (lo b) (hi b)) ω).descFactorial 2) :
    ∫ ω, (pairCount ω : ℝ) ∂M.P ≤
      ∑ b ∈ bins,
        (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
          (hi b - lo b)) ^ 2 := by
  apply integral_pairCount_le_sum_sq_of_factorialMoments M.P bins pairCount
    (fun b ω => BlockGUE.intervalCount M A₀ (Set.Icc (lo b) (hi b)) ω)
    (fun b => input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
      (hi b - lo b))
  · exact hpairInt
  · intro b hb
    exact input.factorialIntegrable hd M A₀ (lo b) (hi b) 2
  · exact hcover
  · intro b hb
    exact psss_closePairCount input hd M A₀ (lo b) (hi b) (hlohi b hb)

/-- Uniform-width consequence.  If at most `m` windows of width `w` cover all
ordered close pairs, their expected number is at most
`m (C · dimension · w)^2`. -/
theorem psss_pairCount_le_card_mul_windowSquare
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    {κ : Type v} [DecidableEq κ] (bins : Finset κ)
    (lo hi : κ → ℝ) (hlohi : ∀ b ∈ bins, lo b ≤ hi b)
    (w : ℝ) (hw : 0 ≤ w)
    (hwidth : ∀ b ∈ bins, hi b - lo b ≤ w)
    (pairCount : M.Ω → ℕ)
    (hpairInt : Integrable (fun ω => (pairCount ω : ℝ)) M.P)
    (hcover : ∀ ω, pairCount ω ≤
      ∑ b ∈ bins,
        (BlockGUE.intervalCount M A₀ (Set.Icc (lo b) (hi b)) ω).descFactorial 2) :
    ∫ ω, (pairCount ω : ℝ) ∂M.P ≤
      (bins.card : ℝ) *
        (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * w) ^ 2 := by
  calc
    (∫ ω, (pairCount ω : ℝ) ∂M.P) ≤
        ∑ b ∈ bins,
          (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
            (hi b - lo b)) ^ 2 :=
      psss_pairCount_le_sum_windowSquares input hd M A₀ bins lo hi hlohi
        pairCount hpairInt hcover
    _ ≤ ∑ _b ∈ bins,
          (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * w) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply (sq_le_sq₀
        (mul_nonneg
          (mul_nonneg input.C_nonneg (Nat.cast_nonneg _))
          (sub_nonneg.mpr (hlohi b hb)))
        (mul_nonneg
          (mul_nonneg input.C_nonneg (Nat.cast_nonneg _)) hw)).2
      exact mul_le_mul_of_nonneg_left (hwidth b hb)
        (mul_nonneg input.C_nonneg (Nat.cast_nonneg _))
    _ = (bins.card : ℝ) *
        (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * w) ^ 2 := by
      simp

end CoareaNative.BlockBand
