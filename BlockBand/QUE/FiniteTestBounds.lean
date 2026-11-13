module

public import BlockBand.Foundations.BlockDecomposition

/-!
# Deterministic test bounds for the Haar site bridge

For a test `v` on `B × A` with `|v| ≤ 1` and nonnegative block masses `p` summing to one,
the within-block residual has squared norm at most the block width, and the weighted Haar
residual `Σ_b p_b²/(W(W+1)) Σ_a (v - v̄_b)²` is at most `1/(W+1)` (`haar_weighted_residual_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE

open scoped BigOperators
open BlockBand.Foundations.FiniteBlock

variable {B A : Type*} [Fintype B] [Fintype A] [Nonempty A]

omit [Fintype B] in
/-- Averages preserve the deterministic pointwise absolute-value bound one. -/
theorem average_abs_le_one (v : B × A → ℝ) (hv : ∀ x, |v x| ≤ 1) (b : B) :
    |average v b| ≤ 1 := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  rw [average, abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  calc
    |∑ a : A, v (b, a)| ≤ ∑ a : A, |v (b, a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hv (b, a))
    _ = 1 * (Fintype.card A : ℝ) := by simp

omit [Fintype B] in
/-- Finite variance identity `Σ_a (v_a - v̄)² = Σ_a v_a² - W v̄²` (deterministic). -/
theorem sum_centered_sq (v : B × A → ℝ) (b : B) :
    (∑ a : A, centeredPart v (b, a) ^ 2) =
      (∑ a : A, v (b, a) ^ 2) - (Fintype.card A : ℝ) * (average v b) ^ 2 := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).ne'
  have hsum : (∑ a : A, v (b, a)) = (Fintype.card A : ℝ) * average v b := by
    unfold average
    field_simp
  have hterm (a : A) : centeredPart v (b, a) ^ 2 =
      v (b, a) ^ 2 - (2 * average v b) * v (b, a) + (average v b) ^ 2 := by
    simp only [centeredPart, constantPart]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  ring

omit [Fintype B] in
/-- The squared within-block residual norm is at most the block width. -/
theorem sum_centered_sq_le_card (v : B × A → ℝ)
    (hv : ∀ x, |v x| ≤ 1) (b : B) :
    (∑ a : A, centeredPart v (b, a) ^ 2) ≤ (Fintype.card A : ℝ) := by
  rw [sum_centered_sq]
  have hraw : (∑ a : A, v (b, a) ^ 2) ≤ (Fintype.card A : ℝ) := by
    calc
      (∑ a : A, v (b, a) ^ 2) ≤ ∑ _a : A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        have hprod := mul_le_mul (hv (b, a)) (hv (b, a))
          (abs_nonneg (v (b, a))) (show (0 : ℝ) ≤ 1 by norm_num)
        simpa only [← pow_two, sq_abs, one_pow] using hprod
      _ = (Fintype.card A : ℝ) := by simp
  have hnonneg : 0 ≤ (Fintype.card A : ℝ) * (average v b) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

omit [Nonempty A] in
/-- The sum of squared nonnegative block masses is at most one. -/
theorem sum_mass_sq_le_one (p : B → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b : B, p b = 1) :
    (∑ b : B, p b ^ 2) ≤ 1 := by
  have hpone (b : B) : p b ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun c _ => hp c) (Finset.mem_univ b)
  calc
    (∑ b : B, p b ^ 2) ≤ ∑ b : B, p b := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left (hpone b) (hp b)
    _ = 1 := hsum

/-- The deterministic part of the Haar residual bound is `1/(W+1)`. The coefficient is the Haar
complex-sphere diagonal excess `p_b²/[W(W+1)]`; only the simplex and test bounds are used. -/
theorem haar_weighted_residual_le (p : B → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b : B, p b = 1) (v : B × A → ℝ) (hv : ∀ x, |v x| ≤ 1) :
    (∑ b : B, (p b ^ 2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1))) *
      ∑ a : A, centeredPart v (b, a) ^ 2) ≤
        1 / ((Fintype.card A : ℝ) + 1) := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hden : 0 < (Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1) := by
    positivity
  calc
    (∑ b : B, (p b ^ 2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1))) *
      ∑ a : A, centeredPart v (b, a) ^ 2) ≤
        ∑ b : B, (p b ^ 2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1))) *
          (Fintype.card A : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (sum_centered_sq_le_card v hv b)
        (div_nonneg (sq_nonneg _) hden.le)
    _ = (∑ b : B, p b ^ 2) / ((Fintype.card A : ℝ) + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      field_simp
    _ ≤ 1 / ((Fintype.card A : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right (sum_mass_sq_le_one p hp hsum) (by positivity)

end BlockBand.QUE
