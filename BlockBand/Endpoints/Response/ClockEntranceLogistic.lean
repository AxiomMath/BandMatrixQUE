module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discrete logistic comparison for the fractional clock entrance

A real sequence `y ≥ 0` obeying, on the steps `j₀ ≤ n < j₂`,
`y_{n+1} ≤ y_n + h (C y_n - c y_n² + C)` with `C ≥ 0`, `c > 0`, step `h > 0` and
`h C B ≤ 1` for the level `B = ce_logisticLevel C c = 2 + 4(C+1)/c`, satisfies
`y_n ≤ B + 2/(cτ)` whenever `j₀ ≤ n ≤ j₂` and `0 < τ ≤ h (n - j₀)`
(`ce_logistic_bound`): with `h = 1/W` and `n - j₀ ≥ τW` this is the bound `C(1 + τ⁻¹)` at
elapsed time `τ`, independent of the initial value `y_{j₀}` (in particular of the initial
bound `C W^{1-p}`). Mechanism (`ce_logistic_dichotomy`): above the level `B - 1` the
quadratic term dominates, `y_{n+1} ≤ y_n - (hc/2) y_n²`, hence `1/y` grows by `hc/2` per step;
once `y_n ≤ B` it stays `≤ B`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

/-- The absorbing level `B = 2 + 4(C+1)/c` of the discrete logistic comparison. -/
def ce_logisticLevel (C c : ℝ) : ℝ := 2 + 4 * (C + 1) / c

/-- Above `B - 1 = 1 + 4(C+1)/c` the quadratic term dominates:
`C y - c y² + C ≤ -(c/2) y²`. -/
theorem ce_logistic_drift_le {C c y : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hy : ce_logisticLevel C c - 1 ≤ y) : C * y - c * y ^ 2 + C ≤ -(c / 2 * y ^ 2) := by
  unfold ce_logisticLevel at hy
  have hq : 0 ≤ 4 * (C + 1) / c := div_nonneg (by linarith) hc.le
  have hy1 : 1 ≤ y := by linarith
  have hcy : 4 * (C + 1) ≤ c * y := by
    have h4 : 4 * (C + 1) / c ≤ y := by linarith
    rw [div_le_iff₀ hc] at h4
    linarith
  nlinarith

/-- **Dichotomy of the discrete logistic comparison.** Under the one-step recursion on
`j₀ ≤ n < j₂`, at every `n = j₀ + k ≤ j₂` either `y_n ≤ B` or `y_n > 0` and
`(hc/2) k ≤ 1/y_n`. -/
theorem ce_logistic_dichotomy {C c h : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hh : 0 < h)
    (hsmall : h * C * ce_logisticLevel C c ≤ 1) (y : ℕ → ℝ) (hy0 : ∀ n, 0 ≤ y n)
    (j₀ j₂ : ℕ)
    (hrec : ∀ n, j₀ ≤ n → n < j₂ → y (n + 1) ≤ y n + h * (C * y n - c * y n ^ 2 + C)) :
    ∀ k : ℕ, j₀ + k ≤ j₂ → y (j₀ + k) ≤ ce_logisticLevel C c ∨
      (0 < y (j₀ + k) ∧ h * c / 2 * k ≤ 1 / y (j₀ + k)) := by
  set B := ce_logisticLevel C c with hB
  have hBpos : 2 ≤ B := by
    have : 0 ≤ 4 * (C + 1) / c := div_nonneg (by linarith) hc.le
    rw [hB]; unfold ce_logisticLevel; linarith
  -- one step from `y_n`
  have hdown : ∀ n, j₀ ≤ n → n < j₂ → B - 1 ≤ y n →
      y (n + 1) ≤ y n - h * c / 2 * y n ^ 2 := by
    intro n h0 h2 hyn
    have hd := ce_logistic_drift_le hC hc hyn
    have := hrec n h0 h2
    have : h * (C * y n - c * y n ^ 2 + C) ≤ h * (-(c / 2 * y n ^ 2)) :=
      mul_le_mul_of_nonneg_left hd hh.le
    nlinarith
  intro k
  induction k with
  | zero =>
    intro _
    by_cases hyB : y (j₀ + 0) ≤ B
    · exact Or.inl hyB
    · refine Or.inr ⟨by linarith [not_le.mp hyB], ?_⟩
      simp only [Nat.cast_zero, mul_zero]
      exact div_nonneg zero_le_one (hy0 _)
  | succ k ih =>
    intro hk
    have hn : j₀ + k < j₂ := by omega
    have hn0 : j₀ ≤ j₀ + k := Nat.le_add_right _ _
    have hsucc : j₀ + (k + 1) = j₀ + k + 1 := by omega
    rw [hsucc]
    set a := y (j₀ + k) with ha
    set a' := y (j₀ + k + 1) with ha'
    have hrec' := hrec (j₀ + k) hn0 hn
    rcases ih (by omega) with hle | ⟨hapos, hinv⟩
    · left
      by_cases hlow : a < B - 1
      · have h1 : h * (C * a - c * a ^ 2 + C) ≤ h * (C * a + C) := by
          apply mul_le_mul_of_nonneg_left _ hh.le
          nlinarith [sq_nonneg a]
        have h2 : h * (C * a + C) ≤ h * C * B := by
          have : C * a + C ≤ C * B := by nlinarith
          calc h * (C * a + C) ≤ h * (C * B) := mul_le_mul_of_nonneg_left this hh.le
            _ = h * C * B := by ring
        linarith
      · have := hdown (j₀ + k) hn0 hn (not_lt.mp hlow)
        have : 0 ≤ h * c / 2 * a ^ 2 := by positivity
        linarith
    · by_cases hlow : a ≤ B
      · -- impossible to leave `B` from below (same computation as above)
        left
        by_cases hlow' : a < B - 1
        · have h1 : h * (C * a - c * a ^ 2 + C) ≤ h * (C * a + C) := by
            apply mul_le_mul_of_nonneg_left _ hh.le
            nlinarith [sq_nonneg a]
          have h2 : h * (C * a + C) ≤ h * C * B := by
            have : C * a + C ≤ C * B := by nlinarith
            calc h * (C * a + C) ≤ h * (C * B) := mul_le_mul_of_nonneg_left this hh.le
              _ = h * C * B := by ring
          linarith
        · have := hdown (j₀ + k) hn0 hn (not_lt.mp hlow')
          have : 0 ≤ h * c / 2 * a ^ 2 := by positivity
          linarith
      · have haB : B < a := not_le.mp hlow
        have hstep := hdown (j₀ + k) hn0 hn (by linarith)
        by_cases ha'B : a' ≤ B
        · exact Or.inl ha'B
        · right
          have ha'pos : 0 < a' := by linarith [not_le.mp ha'B]
          refine ⟨ha'pos, ?_⟩
          set κ := h * c / 2 with hκ
          have hκ0 : 0 < κ := by positivity
          -- `1/a + κ ≤ 1/a'`
          have hfrac : a' / a ≤ 1 - κ * a := by
            rw [div_le_iff₀ hapos]; nlinarith
          have hka' : κ * a' ≤ κ * a - κ * (κ * a ^ 2) := by
            have : a' ≤ a - κ * a ^ 2 := hstep
            nlinarith
          have hkey : (1 / a + κ) * a' ≤ 1 := by
            have : (1 / a + κ) * a' = a' / a + κ * a' := by ring
            rw [this]
            nlinarith [sq_nonneg (κ * a)]
          have hkey' : 1 / a + κ ≤ 1 / a' := by
            rw [le_div_iff₀ ha'pos]; exact hkey
          have : κ * ((k + 1 : ℕ) : ℝ) = κ * k + κ := by push_cast; ring
          rw [this]
          linarith

/-- **Discrete logistic comparison**. Under the one-step recursion
`y_{n+1} ≤ y_n + h (C y_n - c y_n² + C)` on `j₀ ≤ n < j₂` (`C ≥ 0`, `c > 0`, `h > 0`,
`h C B ≤ 1`, `y ≥ 0`), every `j₀ ≤ n ≤ j₂` with `0 < τ ≤ h (n - j₀)` satisfies
`y_n ≤ B + 2/(cτ)`, `B = ce_logisticLevel C c`. -/
theorem ce_logistic_bound {C c h : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hh : 0 < h)
    (hsmall : h * C * ce_logisticLevel C c ≤ 1) (y : ℕ → ℝ) (hy0 : ∀ n, 0 ≤ y n)
    (j₀ j₂ : ℕ)
    (hrec : ∀ n, j₀ ≤ n → n < j₂ → y (n + 1) ≤ y n + h * (C * y n - c * y n ^ 2 + C))
    (n : ℕ) (hn0 : j₀ ≤ n) (hn2 : n ≤ j₂) (τ : ℝ) (hτ : 0 < τ)
    (hτn : τ ≤ h * ((n : ℝ) - j₀)) :
    y n ≤ ce_logisticLevel C c + 2 / (c * τ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn0
  have hcast : ((j₀ + k : ℕ) : ℝ) - j₀ = k := by push_cast; ring
  rw [hcast] at hτn
  have h2 : 0 ≤ 2 / (c * τ) := by positivity
  rcases ce_logistic_dichotomy hC hc hh hsmall y hy0 j₀ j₂ hrec k hn2 with hle | ⟨hpos, hinv⟩
  · linarith
  · have hcτ : c * τ / 2 ≤ 1 / y (j₀ + k) := by
      have : c * τ / 2 ≤ h * c / 2 * k := by
        have := mul_le_mul_of_nonneg_left hτn (by positivity : (0 : ℝ) ≤ c / 2)
        nlinarith
      linarith
    rw [le_div_iff₀ hpos] at hcτ
    have hyle : y (j₀ + k) ≤ 2 / (c * τ) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ ce_logisticLevel C c := by
      unfold ce_logisticLevel
      have : 0 ≤ 4 * (C + 1) / c := div_nonneg (by linarith) hc.le
      linarith
    linarith

end BlockBand.Endpoints
