module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# One-sided second-order Taylor bound on `[0,1]`

**`taylor2_upper`**: if `f, f₁, f₂` have derivatives `f₁, f₂, f₃` at every point of `[0,1]` and
`f₃ ≤ M` there, then `f 1 ≤ f 0 + f₁ 0 + f₂ 0 / 2 + M / 6`. The proof is three monotonicity
steps (`monotoneOn_of_hasDerivWithinAt_nonneg`). Only the upper bound is needed: the Lyapunov
step `lyap_step` bounds `E F(T_{r+1})` from above.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open Set

/-- Monotonicity on `[0,1]` from a nonnegative derivative at every point of `[0,1]`. -/
theorem monotoneOn_Icc01 {G G' : ℝ → ℝ} (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' t) t)
    (h0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ G' t) : MonotoneOn G (Icc 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := G') (convex_Icc 0 1)
    (fun t ht => (hG t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hG t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
  · rw [interior_Icc] at ht
    exact h0 t ht

/-- **One-sided Taylor bound of order two with a third-derivative bound.** -/
theorem taylor2_upper {f f₁ f₂ f₃ : ℝ → ℝ} {M : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, f₃ t ≤ M) :
    f 1 ≤ f 0 + f₁ 0 + f₂ 0 / 2 + M / 6 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- step 2: `f₂ t - f₂ 0 ≤ M t`
  have m2 : MonotoneOn (fun t => M * t - (f₂ t - f₂ 0)) (Icc 0 1) := by
    refine monotoneOn_Icc01 (G' := fun t => M - f₃ t) (fun t ht => ?_) (fun t ht => ?_)
    · have := ((hasDerivAt_id' t).const_mul M).sub ((hf₂ t ht).sub_const (f₂ 0))
      convert this using 1; ring
    · simp only [sub_nonneg]; exact hM t (Ioo_subset_Icc_self ht)
  have b2 : ∀ t ∈ Icc (0 : ℝ) 1, f₂ t - f₂ 0 ≤ M * t := fun t ht => by
    have := m2 h0 ht ht.1
    simp only [mul_zero, sub_self] at this
    linarith
  -- step 1: `f₁ t - f₁ 0 - f₂ 0 t ≤ M t² / 2`
  have m1 : MonotoneOn (fun t => M * t ^ 2 / 2 - (f₁ t - f₁ 0 - f₂ 0 * t)) (Icc 0 1) := by
    refine monotoneOn_Icc01 (G' := fun t => M * t - (f₂ t - f₂ 0)) (fun t ht => ?_)
      (fun t ht => ?_)
    · have h1 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
      have h2 := ((hf₁ t ht).sub_const (f₁ 0)).sub ((hasDerivAt_id' t).const_mul (f₂ 0))
      convert h1.sub h2 using 1
      simp only [Nat.cast_ofNat]
      ring
    · simp only [sub_nonneg]; exact b2 t (Ioo_subset_Icc_self ht)
  have b1 : ∀ t ∈ Icc (0 : ℝ) 1, f₁ t - f₁ 0 - f₂ 0 * t ≤ M * t ^ 2 / 2 := fun t ht => by
    have := m1 h0 ht ht.1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      sub_self] at this
    linarith
  -- step 0
  have m0 : MonotoneOn (fun t => M * t ^ 3 / 6 -
      (f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2)) (Icc 0 1) := by
    refine monotoneOn_Icc01 (G' := fun t => M * t ^ 2 / 2 - (f₁ t - f₁ 0 - f₂ 0 * t))
      (fun t ht => ?_) (fun t ht => ?_)
    · have h1 := ((hasDerivAt_pow 3 t).const_mul M).div_const 6
      have h2 := (((hf t ht).sub_const (f 0)).sub ((hasDerivAt_id' t).const_mul (f₁ 0))).sub
        (((hasDerivAt_pow 2 t).const_mul (f₂ 0)).div_const 2)
      convert h1.sub h2 using 1
      simp only [Nat.cast_ofNat]
      ring
    · simp only [sub_nonneg]; exact b1 t (Ioo_subset_Icc_self ht)
  have := m0 h0 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    sub_self, one_pow, mul_one] at this
  linarith

end BlockBand.Transmission.LawDecay
