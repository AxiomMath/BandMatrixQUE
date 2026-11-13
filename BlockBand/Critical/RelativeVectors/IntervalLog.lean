module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The number of dyadic heights

Elementary. `dyK N = log₂ ⌊N^{1/100}⌋` satisfies `2^K h ≤ 1 < 2^{K+1} h` for `h = N^{-1/100}`
(`dyK_spec`), and the logarithmic factor is absorbed by `N^ε`: `N h (K + 2) ≤ 147 N^{1-α+ε}`
(`nhK_le`, from `log x ≤ x^ε/ε` and `log 2 > 0.69`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

/-- The number of dyadic heights: `log₂ ⌊N^{1/100}⌋`. -/
def dyK (N : ℕ) : ℕ := Nat.log 2 ⌊(N : ℝ) ^ (1 / 100 : ℝ)⌋₊

theorem dyK_spec {N : ℕ} (hN : 0 < N) :
    1 < 2 ^ (dyK N + 1) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      2 ^ dyK N * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set y := (N : ℝ) ^ (1 / 100 : ℝ) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hy0 : 0 < y := by linarith
  have hinv : (N : ℝ) ^ (-(1 / 100 : ℝ)) = y⁻¹ := by rw [Real.rpow_neg hNr.le]
  rw [hinv]
  set n := ⌊y⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hy1)
  have hpow : 2 ^ dyK N ≤ n := Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.1 hn1)
  have hlt : n < 2 ^ (dyK N + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  constructor
  · have : (n : ℝ) + 1 ≤ 2 ^ (dyK N + 1) := by exact_mod_cast hlt
    rw [← div_eq_mul_inv, one_lt_div hy0]
    linarith
  · have : ((2 ^ dyK N : ℕ) : ℝ) ≤ n := by exact_mod_cast hpow
    push_cast at this
    rw [← div_eq_mul_inv, div_le_one hy0]
    linarith

theorem dyK_add_two_le {N : ℕ} (hN : 0 < N) :
    (dyK N : ℝ) + 2 ≤ 147 * (N : ℝ) ^ (1 / 10000 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set y := (N : ℝ) ^ (1 / 100 : ℝ) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hy0 : 0 < y := by linarith
  have hpow : ((2 : ℝ) ^ dyK N) ≤ y := by
    have h1 : 2 ^ dyK N ≤ ⌊y⌋₊ := Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.1
      (Nat.le_floor (by exact_mod_cast hy1)))
    have h2 : ((2 ^ dyK N : ℕ) : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le hy0.le)
  have hlog : (dyK N : ℝ) * Real.log 2 ≤ Real.log y := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hlogy : Real.log y = (1 / 100) * Real.log N := by
    rw [hy, Real.log_rpow hNr]
  have hlogN : Real.log N ≤ (N : ℝ) ^ (1 / 10000 : ℝ) / (1 / 10000) :=
    Real.log_le_rpow_div hNr.le (by norm_num)
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hε : 1 ≤ (N : ℝ) ^ (1 / 10000 : ℝ) := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hK : (dyK N : ℝ) * 0.69 ≤ 100 * (N : ℝ) ^ (1 / 10000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ dyK N := Nat.cast_nonneg _
    have : (dyK N : ℝ) * 0.69 ≤ (dyK N : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le h0
    rw [hlogy] at hlog
    have e : (1 / 100 : ℝ) * ((N : ℝ) ^ (1 / 10000 : ℝ) / (1 / 10000)) =
        100 * (N : ℝ) ^ (1 / 10000 : ℝ) := by ring
    nlinarith
  nlinarith

theorem nhK_le {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * ((dyK N : ℝ) + 2) ≤
      147 * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := dyK_add_two_le hN
  have e : (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) =
      (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * (N : ℝ) ^ (1 / 10000 : ℝ) := by
    rw [Real.rpow_add hNr, Real.rpow_sub hNr, Real.rpow_one, Real.rpow_neg hNr.le]
    field_simp
  rw [e]
  have h0 : 0 ≤ (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by positivity
  calc (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * ((dyK N : ℝ) + 2)
      ≤ (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * (147 * (N : ℝ) ^ (1 / 10000 : ℝ)) :=
        mul_le_mul_of_nonneg_left h h0
    _ = _ := by ring

end BlockBand.Critical.RelativeVectors
