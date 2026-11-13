module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Discrete higher logistic comparison

A real sequence `y ≥ 0` obeying, on the steps `j₀ ≤ n < j₂`,
`y_{n+1} ≤ y_n + h (C y_n - c y_n^{1+θ} + C)` with `0 < θ ≤ 1` (`θ = 1/r`), `C ≥ 0`, `c > 0`,
`h > 0` and `h C B ≤ 1` for the level `B = rhn_logisticLevel C c r = 2 + (4(C+1)/c)^r`, satisfies
`y_n ≤ B + (2/(θcτ))^r` whenever `j₀ ≤ n ≤ j₂` and `0 < τ ≤ h (n - j₀)`
(`rhn_logistic_bound`), independently of the initial value. Mechanism
(`rhn_logistic_dichotomy`): above `B - 1`, `y_{n+1} ≤ y_n - (hc/2) y_n^{1+θ}`, hence by
Bernoulli `(1 - u)^θ ≤ 1 - θu` the quantity `1/y^θ` grows by at least `θhc/2` per step; once
`y_n ≤ B` it stays `≤ B`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

/-- The absorbing level `B = 2 + (4(C+1)/c)^r` of the higher discrete logistic comparison. -/
def rhn_logisticLevel (C c r : ℝ) : ℝ := 2 + (4 * (C + 1) / c) ^ r

theorem rhn_logisticLevel_ge_two {C c r : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    2 ≤ rhn_logisticLevel C c r := by
  unfold rhn_logisticLevel
  have : 0 ≤ (4 * (C + 1) / c) ^ r := Real.rpow_nonneg (div_nonneg (by linarith) hc.le) _
  linarith

/-- Above `B - 1` the power term dominates: `C y - c y^{1+θ} + C ≤ -(c/2) y^{1+θ}`
(`θ = 1/r`, `r > 0`). -/
theorem rhn_logistic_drift_le {C c r y : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hr : 0 < r)
    (hy : rhn_logisticLevel C c r - 1 ≤ y) :
    C * y - c * y ^ (1 + 1 / r) + C ≤ -(c / 2 * y ^ (1 + 1 / r)) := by
  unfold rhn_logisticLevel at hy
  set X := 4 * (C + 1) / c with hX
  have hX0 : 0 ≤ X := div_nonneg (by linarith) hc.le
  have hXr : 0 ≤ X ^ r := Real.rpow_nonneg hX0 _
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hyX : X ^ r ≤ y := by linarith
  have hθ : X ≤ y ^ (1 / r) := by
    have h := Real.rpow_le_rpow hXr hyX (by positivity : (0 : ℝ) ≤ 1 / r)
    rwa [← Real.rpow_mul hX0, mul_one_div_cancel hr.ne', Real.rpow_one] at h
  have hsplit : y ^ (1 + 1 / r) = y * y ^ (1 / r) := by
    rw [Real.rpow_add hy0, Real.rpow_one]
  have hcX : c * X = 4 * (C + 1) := by rw [hX]; field_simp
  rw [hsplit]
  have h1 : c * X * y ≤ c * (y * y ^ (1 / r)) := by
    have := mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ c * y)
    nlinarith
  nlinarith

/-- Bernoulli step: if `0 < a'`, `a' ≤ a - κ a^{1+θ}` with `κ ≥ 0`, `0 < θ ≤ 1`, `a > 0`, then
`1/a^θ + θκ ≤ 1/a'^θ`. -/
theorem rhn_inv_rpow_step {a a' κ θ : ℝ} (ha : 0 < a) (ha' : 0 < a') (hκ : 0 ≤ κ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hstep : a' ≤ a - κ * a ^ (1 + θ)) :
    1 / a ^ θ + θ * κ ≤ 1 / a' ^ θ := by
  set u := κ * a ^ θ with hu
  have hpow : a ^ (1 + θ) = a * a ^ θ := by rw [Real.rpow_add ha, Real.rpow_one]
  have haθ : 0 < a ^ θ := Real.rpow_pos_of_pos ha θ
  have hu0 : 0 ≤ u := by positivity
  have hstep' : a' ≤ a * (1 - u) := by rw [hpow] at hstep; rw [hu]; nlinarith
  have hu1 : u < 1 := by
    by_contra h
    have : a * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith [not_lt.mp h])
    linarith
  -- `a'^θ ≤ a^θ (1 - θ u)`
  have hb : (1 - u) ^ θ ≤ 1 - θ * u := by
    have := rpow_one_add_le_one_add_mul_self (s := -u) (p := θ) (by linarith) hθ.le hθ1
    simpa [sub_eq_add_neg] using this
  have ha'θ : a' ^ θ ≤ a ^ θ * (1 - θ * u) := by
    calc a' ^ θ ≤ (a * (1 - u)) ^ θ := Real.rpow_le_rpow ha'.le hstep' hθ.le
      _ = a ^ θ * (1 - u) ^ θ := Real.mul_rpow ha.le (by linarith)
      _ ≤ a ^ θ * (1 - θ * u) := mul_le_mul_of_nonneg_left hb haθ.le
  have ha'θ0 : 0 < a' ^ θ := Real.rpow_pos_of_pos ha' θ
  have hθu : θ * u < 1 := by nlinarith
  have hθu0 : 0 ≤ θ * u := by positivity
  -- `1/(a^θ (1 - v)) ≥ (1 + v)/a^θ`
  rw [le_div_iff₀ ha'θ0]
  have hkey : (1 / a ^ θ + θ * κ) * (a ^ θ * (1 - θ * u)) ≤ 1 := by
    have e : (1 / a ^ θ + θ * κ) * (a ^ θ * (1 - θ * u)) = (1 + θ * u) * (1 - θ * u) := by
      rw [hu]; field_simp
    rw [e]; nlinarith
  calc (1 / a ^ θ + θ * κ) * a' ^ θ ≤ (1 / a ^ θ + θ * κ) * (a ^ θ * (1 - θ * u)) :=
        mul_le_mul_of_nonneg_left ha'θ (by positivity)
    _ ≤ 1 := hkey

/-- Dichotomy of the higher discrete logistic comparison. Under the one-step recursion on
`j₀ ≤ n < j₂`, at every `n = j₀ + k ≤ j₂` either `y_n ≤ B` or `y_n > 0` and
`θ (hc/2) k ≤ 1/y_n^θ`, `θ = 1/r`. -/
theorem rhn_logistic_dichotomy {C c h r : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hh : 0 < h)
    (hr : 1 ≤ r) (hsmall : h * C * rhn_logisticLevel C c r ≤ 1) (y : ℕ → ℝ)
    (hy0 : ∀ n, 0 ≤ y n) (j₀ j₂ : ℕ)
    (hrec : ∀ n, j₀ ≤ n → n < j₂ →
      y (n + 1) ≤ y n + h * (C * y n - c * y n ^ (1 + 1 / r) + C)) :
    ∀ k : ℕ, j₀ + k ≤ j₂ → y (j₀ + k) ≤ rhn_logisticLevel C c r ∨
      (0 < y (j₀ + k) ∧ 1 / r * (h * c / 2) * k ≤ 1 / y (j₀ + k) ^ (1 / r)) := by
  set B := rhn_logisticLevel C c r with hB
  have hr0 : 0 < r := by linarith
  have hBpos : 2 ≤ B := rhn_logisticLevel_ge_two hC hc
  have hθ : 0 < 1 / r := by positivity
  have hθ1 : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have hdown : ∀ n, j₀ ≤ n → n < j₂ → B - 1 ≤ y n →
      y (n + 1) ≤ y n - h * c / 2 * y n ^ (1 + 1 / r) := by
    intro n h0 h2 hyn
    have hd := rhn_logistic_drift_le hC hc hr0 hyn
    have := hrec n h0 h2
    have : h * (C * y n - c * y n ^ (1 + 1 / r) + C) ≤ h * (-(c / 2 * y n ^ (1 + 1 / r))) :=
      mul_le_mul_of_nonneg_left hd hh.le
    nlinarith
  -- staying below `B`
  have hstay : ∀ n, j₀ ≤ n → n < j₂ → y n ≤ B → y (n + 1) ≤ B := by
    intro n h0 h2 hyn
    by_cases hlow : y n < B - 1
    · have hpw : 0 ≤ y n ^ (1 + 1 / r) := Real.rpow_nonneg (hy0 n) _
      have h1 : h * (C * y n - c * y n ^ (1 + 1 / r) + C) ≤ h * (C * y n + C) := by
        apply mul_le_mul_of_nonneg_left _ hh.le
        nlinarith
      have h2' : h * (C * y n + C) ≤ h * C * B := by
        have : C * y n + C ≤ C * B := by nlinarith
        calc h * (C * y n + C) ≤ h * (C * B) := mul_le_mul_of_nonneg_left this hh.le
          _ = h * C * B := by ring
      have := hrec n h0 h2
      linarith
    · have := hdown n h0 h2 (not_lt.mp hlow)
      have : 0 ≤ h * c / 2 * y n ^ (1 + 1 / r) := by
        have := Real.rpow_nonneg (hy0 n) (1 + 1 / r); positivity
      linarith
  intro k
  induction k with
  | zero =>
    intro _
    by_cases hyB : y (j₀ + 0) ≤ B
    · exact Or.inl hyB
    · refine Or.inr ⟨by linarith [not_le.mp hyB], ?_⟩
      simp only [Nat.cast_zero, mul_zero]
      exact div_nonneg zero_le_one (Real.rpow_nonneg (hy0 _) _)
  | succ k ih =>
    intro hk
    have hn : j₀ + k < j₂ := by omega
    have hn0 : j₀ ≤ j₀ + k := Nat.le_add_right _ _
    have hsucc : j₀ + (k + 1) = j₀ + k + 1 := by omega
    rw [hsucc]
    rcases ih (by omega) with hle | ⟨hapos, hinv⟩
    · exact Or.inl (hstay _ hn0 hn hle)
    · by_cases hlow : y (j₀ + k) ≤ B
      · exact Or.inl (hstay _ hn0 hn hlow)
      · have haB : B < y (j₀ + k) := not_le.mp hlow
        have hstep := hdown (j₀ + k) hn0 hn (by linarith)
        by_cases ha'B : y (j₀ + k + 1) ≤ B
        · exact Or.inl ha'B
        · right
          have ha'pos : 0 < y (j₀ + k + 1) := by linarith [not_le.mp ha'B]
          refine ⟨ha'pos, ?_⟩
          have hs := rhn_inv_rpow_step hapos ha'pos (by positivity : 0 ≤ h * c / 2) hθ hθ1
            (by rw [mul_comm (h * c / 2)] at hstep ⊢; linarith)
          have : 1 / r * (h * c / 2) * ((k + 1 : ℕ) : ℝ) =
              1 / r * (h * c / 2) * k + 1 / r * (h * c / 2) := by push_cast; ring
          rw [this]
          linarith

/-- Higher discrete logistic comparison. Under the one-step recursion
`y_{n+1} ≤ y_n + h (C y_n - c y_n^{1+1/r} + C)` on `j₀ ≤ n < j₂` (`r ≥ 1`, `C ≥ 0`, `c > 0`,
`h > 0`, `h C B ≤ 1`, `y ≥ 0`), every `j₀ ≤ n ≤ j₂` with `0 < τ ≤ h (n - j₀)` satisfies
`y_n ≤ B + (2r/(cτ))^r`, `B = rhn_logisticLevel C c r`. At `r = 1` this is
`ce_logistic_bound` up to the level. -/
theorem rhn_logistic_bound {C c h r : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hh : 0 < h) (hr : 1 ≤ r)
    (hsmall : h * C * rhn_logisticLevel C c r ≤ 1) (y : ℕ → ℝ) (hy0 : ∀ n, 0 ≤ y n)
    (j₀ j₂ : ℕ)
    (hrec : ∀ n, j₀ ≤ n → n < j₂ →
      y (n + 1) ≤ y n + h * (C * y n - c * y n ^ (1 + 1 / r) + C))
    (n : ℕ) (hn0 : j₀ ≤ n) (hn2 : n ≤ j₂) (τ : ℝ) (hτ : 0 < τ)
    (hτn : τ ≤ h * ((n : ℝ) - j₀)) :
    y n ≤ rhn_logisticLevel C c r + (2 * r / (c * τ)) ^ r := by
  have hr0 : 0 < r := by linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn0
  have hcast : ((j₀ + k : ℕ) : ℝ) - j₀ = k := by push_cast; ring
  rw [hcast] at hτn
  have h2 : 0 ≤ (2 * r / (c * τ)) ^ r := Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ rhn_logisticLevel C c r := by linarith [rhn_logisticLevel_ge_two (r := r) hC hc]
  rcases rhn_logistic_dichotomy hC hc hh hr hsmall y hy0 j₀ j₂ hrec k hn2 with hle | ⟨hpos, hinv⟩
  · linarith
  · set z := y (j₀ + k) ^ (1 / r) with hz
    have hzpos : 0 < z := Real.rpow_pos_of_pos hpos _
    have hcτ : c * τ / (2 * r) ≤ 1 / z := by
      have : c * τ / (2 * r) ≤ 1 / r * (h * c / 2) * k := by
        have := mul_le_mul_of_nonneg_left hτn (by positivity : (0 : ℝ) ≤ c / (2 * r))
        calc c * τ / (2 * r) = c / (2 * r) * τ := by ring
          _ ≤ c / (2 * r) * (h * k) := this
          _ = 1 / r * (h * c / 2) * k := by field_simp
      linarith
    have hzle : z ≤ 2 * r / (c * τ) := by
      rw [le_div_iff₀ hzpos] at hcτ
      rw [le_div_iff₀ (by positivity)]
      have e : z * (c * τ) = c * τ / (2 * r) * z * (2 * r) := by field_simp
      rw [e]
      calc c * τ / (2 * r) * z * (2 * r) ≤ 1 * (2 * r) :=
            mul_le_mul_of_nonneg_right hcτ (by positivity)
        _ = 2 * r := one_mul _
    have hyz : y (j₀ + k) = z ^ r := by
      rw [hz, ← Real.rpow_mul hpos.le, one_div_mul_cancel hr0.ne', Real.rpow_one]
    have : y (j₀ + k) ≤ (2 * r / (c * τ)) ^ r := by
      rw [hyz]; exact Real.rpow_le_rpow hzpos.le hzle hr0.le
    linarith

end BlockBand.Endpoints
