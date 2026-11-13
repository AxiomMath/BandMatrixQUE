module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Discrete Gronwall for the Lyapunov recursion

**`gronwall`**: if `y_{r+1} ≤ y_r - a(y_r - z) + err_r` for `r ≥ m` with `0 ≤ a ≤ 1`,
`err ≥ 0`, then `y_n - z ≤ (1-a)^{n-m} max(y_m - z, 0) + Σ_{m ≤ r < n} err_r`.
**`one_sub_pow_le_exp`**: `(1-a)^N ≤ e^{-aN}` for `a ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

theorem gronwall {y err : ℕ → ℝ} {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (herr : ∀ r, 0 ≤ err r) (m : ℕ)
    (h : ∀ r, m ≤ r → y (r + 1) ≤ y r - a * (y r - z) + err r) :
    ∀ n, m ≤ n → y n - z ≤ (1 - a) ^ (n - m) * max (y m - z) 0 + ∑ r ∈ Finset.Ico m n, err r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, show n + 1 - m = (n - m) + 1 by omega, pow_succ]
    have hS : 0 ≤ ∑ r ∈ Finset.Ico m n, err r := Finset.sum_nonneg fun r _ => herr r
    have h1a : 0 ≤ 1 - a := by linarith
    have hstep := h n hn
    have hM : 0 ≤ max (y m - z) 0 := le_max_right _ _
    have hp : 0 ≤ (1 - a) ^ (n - m) := pow_nonneg h1a _
    have := mul_le_mul_of_nonneg_left ih h1a
    have : (1 - a) * ∑ r ∈ Finset.Ico m n, err r ≤ ∑ r ∈ Finset.Ico m n, err r :=
      mul_le_of_le_one_left hS (by linarith)
    nlinarith

theorem one_sub_pow_le_exp {a : ℝ} (ha1 : a ≤ 1) (N : ℕ) :
    (1 - a) ^ N ≤ Real.exp (-(a * N)) := by
  have h0 : 0 ≤ 1 - a := by linarith
  have h1 : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  calc (1 - a) ^ N ≤ Real.exp (-a) ^ N := pow_le_pow_left₀ h0 h1 N
    _ = Real.exp (-(a * N)) := by rw [← Real.exp_nat_mul]; ring_nf

end BlockBand.Transmission.LawDecay
