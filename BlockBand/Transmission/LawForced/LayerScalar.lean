module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Exponential

/-!
# Scalar remainders of the one-layer ratio expansion

* **`abs_log_one_add_sub_le`**: for `0 < c ≤ 1` and `ν ≥ c − 1`,
  `|log(1+ν) − ν + ν²/2| ≤ 9|ν|³/c`. Applied to the eigenvalues `ν_k` of the Hermitian
  `N = wR^{1/2}BR^{1/2}` (`1 + N = R^{1/2}(I + wS)R^{1/2} ⪰ c`), it gives the second-order expansion
  of `log det(I + wS)` about `D` for **every** `w ≥ 0` (and `w = −y`, `y < 1`), with remainder
  `Σ|ν_k|³ ≤ ‖N‖‖N‖²_HS`; no power series in `w` is used.
* **`abs_exp_step_le`**: for `0 ≤ F ≤ 1` and `Fe^a ≤ 1`,
  `|Fe^a − F − F(a + a²/2)| ≤ 4|a|³`. With `F = F(T)`, `a = log F(T₊) − log F(T)` this reduces
  `E[ΔF]` to the first two moments of `Δ log F`, with an `E|Δ log F|³ = O(W^{-3/2})` remainder.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

/-- **Global cubic remainder of `log(1+ν)`** on `ν ≥ c − 1`. -/
theorem abs_log_one_add_sub_le {c ν : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hν : c - 1 ≤ ν) :
    |Real.log (1 + ν) - ν + ν ^ 2 / 2| ≤ 9 * |ν| ^ 3 / c := by
  have h3 : 0 ≤ |ν| ^ 3 := by positivity
  have hc9 : 2 * |ν| ^ 3 ≤ 9 * |ν| ^ 3 / c := by
    rw [le_div_iff₀ hc0]; nlinarith
  by_cases hs : |ν| < 1 / 2
  · have h := Real.abs_log_sub_add_sum_range_le (x := -ν) (by rw [abs_neg]; linarith) 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
    have hl : |Real.log (1 + ν) - ν + ν ^ 2 / 2| ≤ |ν| ^ 3 / (1 - |ν|) := by
      convert h using 2; push_cast; ring
    refine hl.trans (le_trans ?_ hc9)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · replace hs := not_lt.1 hs
    have hp : 0 < 1 + ν := by linarith
    have hup : Real.log (1 + ν) ≤ ν := by linarith [Real.log_le_sub_one_of_pos hp]
    have hlo : 1 - (1 + ν)⁻¹ ≤ Real.log (1 + ν) := Real.one_sub_inv_le_log_of_pos hp
    have hinv : 1 - (1 + ν)⁻¹ = ν / (1 + ν) := by field_simp; ring
    have hlo' : -(|ν| / c) ≤ Real.log (1 + ν) := by
      rw [hinv] at hlo
      refine le_trans ?_ hlo
      rcases le_or_gt 0 ν with h0 | h0
      · have : 0 ≤ ν / (1 + ν) := div_nonneg h0 hp.le
        have : 0 ≤ |ν| / c := div_nonneg (abs_nonneg _) hc0.le
        linarith
      · rw [abs_of_neg h0, neg_div, neg_neg, div_le_div_iff₀ hc0 hp]
        nlinarith
    have habs : |Real.log (1 + ν)| ≤ |ν| / c :=
      abs_le.2 ⟨hlo', hup.trans ((le_abs_self ν).trans (le_div_self (abs_nonneg _) hc0 hc1))⟩
    have hsq : 1 / 4 ≤ |ν| ^ 2 := by nlinarith
    have h1 : |ν| ≤ 4 * |ν| ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg ν)]
    have h2 : ν ^ 2 ≤ 2 * |ν| ^ 3 := by
      rw [← sq_abs]; nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg |ν|)]
    have hcd : |ν| / c ≤ 4 * |ν| ^ 3 / c := div_le_div_of_nonneg_right h1 hc0.le
    have hc4 : 4 * |ν| ^ 3 ≤ 4 * |ν| ^ 3 / c := le_div_self (by positivity) hc0 hc1
    calc |Real.log (1 + ν) - ν + ν ^ 2 / 2| ≤ |Real.log (1 + ν)| + |ν| + ν ^ 2 / 2 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 2 / 2)]
          linarith [abs_sub (Real.log (1 + ν)) ν]
      _ ≤ 4 * |ν| ^ 3 / c + 4 * |ν| ^ 3 / c + |ν| ^ 3 / c := by
          have : |ν| ^ 3 ≤ |ν| ^ 3 / c := le_div_self h3 hc0 hc1
          linarith
      _ = 9 * |ν| ^ 3 / c := by ring

/-- **Second-order expansion of `F ↦ Fe^a`** for `0 ≤ F ≤ 1`, `Fe^a ≤ 1`. -/
theorem abs_exp_step_le {F a : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (hF : F * Real.exp a ≤ 1) :
    |F * Real.exp a - F - F * (a + a ^ 2 / 2)| ≤ 4 * |a| ^ 3 := by
  have h3 : 0 ≤ |a| ^ 3 := by positivity
  by_cases ha : |a| ≤ 1
  · have hb := Real.exp_bound ha (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have he : F * Real.exp a - F - F * (a + a ^ 2 / 2) =
        F * (Real.exp a - (1 + a + a ^ 2 / 2)) := by ring
    rw [he, abs_mul, abs_of_nonneg hF0]
    have hb' : |Real.exp a - (1 + a + a ^ 2 / 2)| ≤ |a| ^ 3 * (4 / 18) := by
      convert hb using 2; ring
    calc F * |Real.exp a - (1 + a + a ^ 2 / 2)| ≤ 1 * (|a| ^ 3 * (4 / 18)) :=
          mul_le_mul hF1 hb' (abs_nonneg _) zero_le_one
      _ ≤ 4 * |a| ^ 3 := by linarith
  · replace ha := not_le.1 ha
    have hsq : 1 ≤ |a| ^ 2 := by nlinarith
    have h1 : |a| ≤ |a| ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg a)]
    have h2 : a ^ 2 ≤ |a| ^ 3 := by
      rw [← sq_abs]; nlinarith [mul_le_mul_of_nonneg_left ha.le (sq_nonneg |a|)]
    have he0 : 0 ≤ F * Real.exp a := mul_nonneg hF0 (Real.exp_pos a).le
    have hFa : |F * a| ≤ |a| := by
      rw [abs_mul, abs_of_nonneg hF0]; exact mul_le_of_le_one_left (abs_nonneg _) hF1
    have hFa2 : F * a ^ 2 ≤ a ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hF1
    have hFa2' : 0 ≤ F * a ^ 2 := mul_nonneg hF0 (sq_nonneg _)
    have : |F * Real.exp a - F - F * (a + a ^ 2 / 2)| ≤
        F * Real.exp a + F + |F * a| + F * a ^ 2 / 2 := by
      calc |F * Real.exp a - F - F * (a + a ^ 2 / 2)| =
            |(F * Real.exp a + -F + -(F * a)) + -(F * a ^ 2 / 2)| := by congr 1; ring
        _ ≤ |F * Real.exp a + -F + -(F * a)| + |-(F * a ^ 2 / 2)| := abs_add_le _ _
        _ ≤ (|F * Real.exp a| + |-F| + |-(F * a)|) + |-(F * a ^ 2 / 2)| := by
            gcongr; exact abs_add_three _ _ _
        _ = F * Real.exp a + F + |F * a| + F * a ^ 2 / 2 := by
            rw [abs_neg, abs_neg, abs_neg, abs_of_nonneg he0, abs_of_nonneg hF0,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ F * a ^ 2 / 2)]
    linarith

end BlockBand.Transmission.LawForced
