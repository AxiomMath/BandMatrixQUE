module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discrete logistic comparison

**`logistic_bound`**: if `y ≥ 0` and `y_{r₀+m+1} ≤ y_{r₀+m} - a y_{r₀+m}² + K` for `m < n`
(`a > 0`, `K ≥ 0`), then for `1 ≤ m ≤ n`, `y_{r₀+m} ≤ max(M + K, 2/(am))`,
`M = max(1, 2K/a)`. No initial bound is needed: the quadratic decrement alone brings `y` below
`2/(am)` after `m` steps.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

/-- One step of the comparison. -/
theorem logistic_step {x y' a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy' : 0 ≤ y')
    (hrec : y' ≤ x - a * x ^ 2 + K) (m : ℕ)
    (hxm : m = 0 ∨ x ≤ max (max 1 (2 * K / a) + K) (2 / (a * m))) :
    y' ≤ max (max 1 (2 * K / a) + K) (2 / (a * (m + 1))) := by
  set M := max 1 (2 * K / a)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : 2 * K / a ≤ M := le_max_right _ _
  by_cases hxM : x < M
  · exact le_max_of_le_left (by nlinarith [sq_nonneg x, mul_nonneg ha.le (sq_nonneg x)])
  push Not at hxM
  -- `a x² ≥ 2K`
  have hax : 2 * K ≤ a * x ^ 2 := by
    have h1 : 2 * K ≤ a * M := by rwa [div_le_iff₀' ha] at hMK
    have h2 : a * M ≤ a * x := mul_le_mul_of_nonneg_left hxM ha.le
    have h3 : a * x ≤ a * x ^ 2 := by nlinarith
    linarith
  have hy2 : y' ≤ x - a / 2 * x ^ 2 := by nlinarith
  by_cases hxMK : x ≤ M + K
  · exact le_max_of_le_left (by nlinarith [mul_nonneg ha.le (sq_nonneg x)])
  push Not at hxMK
  refine le_max_of_le_right ?_
  have ham : 0 < a * ((m : ℝ) + 1) := by positivity
  rw [le_div_iff₀ ham]
  set t := a * x with htdef
  have ht0 : 0 ≤ t := by positivity
  -- `a(m+1)(x - (a/2)x²) = (m+1)(t - t²/2)`
  have hkey : a * ((m : ℝ) + 1) * (x - a / 2 * x ^ 2) = ((m : ℝ) + 1) * (t - t ^ 2 / 2) := by
    rw [htdef]; ring
  have hfin : ((m : ℝ) + 1) * (t - t ^ 2 / 2) ≤ 2 := by
    rcases hxm with hm | hxm
    · subst hm; simp; nlinarith [sq_nonneg (t - 1)]
    · have hxb : x ≤ 2 / (a * m) := by
        rcases le_max_iff.mp hxm with h | h
        · linarith
        · exact h
      have hm0 : (0 : ℝ) < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hxb; linarith
        · exact_mod_cast h
      have hmt : (m : ℝ) * t ≤ 2 := by
        rw [htdef]
        have := (le_div_iff₀ (by positivity)).mp hxb
        nlinarith
      by_cases ht2 : t ≤ 2
      · have h1 : 0 ≤ 1 - t / 2 := by linarith
        have := mul_le_mul_of_nonneg_right hmt h1
        nlinarith
      · push Not at ht2
        have : t - t ^ 2 / 2 ≤ 0 := by nlinarith
        have : ((m : ℝ) + 1) * (t - t ^ 2 / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) this
        linarith
  calc y' * (a * ((m : ℝ) + 1)) ≤ (x - a / 2 * x ^ 2) * (a * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hy2 ham.le
    _ = ((m : ℝ) + 1) * (t - t ^ 2 / 2) := by rw [mul_comm, hkey]
    _ ≤ 2 := hfin

/-- **Discrete logistic comparison.** -/
theorem logistic_bound {y : ℕ → ℝ} {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (r₀ n : ℕ)
    (hy : ∀ m, 0 ≤ y (r₀ + m))
    (hrec : ∀ m, m < n → y (r₀ + m + 1) ≤ y (r₀ + m) - a * y (r₀ + m) ^ 2 + K) :
    ∀ m, 1 ≤ m → m ≤ n → y (r₀ + m) ≤ max (max 1 (2 * K / a) + K) (2 / (a * m)) := by
  have key : ∀ m, m ≤ n → m = 0 ∨ y (r₀ + m) ≤ max (max 1 (2 * K / a) + K) (2 / (a * m)) := by
    intro m
    induction m with
    | zero => intro _; exact Or.inl rfl
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have h := logistic_step ha hK (hy k) (hy (k + 1)) (hrec k (by omega)) k hprev
      right
      push_cast
      exact h
  intro m hm1 hmn
  rcases key m hmn with h | h
  · omega
  · exact h

end BlockBand.Transmission.FractionalBulk
