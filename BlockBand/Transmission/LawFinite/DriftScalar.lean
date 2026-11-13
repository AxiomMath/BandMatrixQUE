module

public import BlockBand.Transmission.LawFinite.DriftProb
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Reciprocal drift: scalar bookkeeping

* `drift_err_le`: `refinedErr ≤ (2Li + 3)eq` from `|Tr Qf| ≤ (3/2)Li q`, `q ≤ WLi/4`, `e ≤ 2`;
* `drift_mean_lower`, `drift_inv_mean_le`: from `|m - q/(1+αq/W)| ≤ K_r e q`,
  `α ≤ Li/b` and `K_r e ≤ c₁/2`, `c₁ = (1 + Li²/(4b))⁻¹`: `m ≥ c₁q/2` and
  `m⁻¹ ≤ q⁻¹ + (Li/b)W⁻¹ + (2K_r/c₁²)e/q`;
* `drift_var_le`, `drift_tail_le`: `2σ₂²/m³ ≤ (16C₂²/c₁³)(Wq)⁻¹` and
  `(2σ_N/m)^N ≤ (4C_N/c₁)^N W^{-A}` for `σ = C q/√W`, `A ≤ N/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

theorem drift_err_le {e τ q W Li : ℝ} (he : 0 ≤ e) (he2 : e ≤ 2) (hq : 0 ≤ q) (hW : 1 ≤ W)
    (hτ : τ ≤ 3 / 2 * Li * q) (hqW : q ≤ W * Li / 4) (hτ0 : 0 ≤ τ) :
    e * τ + e ^ 2 * q + e * q ^ 2 / W + W⁻¹ ^ 2 * q ≤ (2 * Li + 3) * (e + W⁻¹ ^ 2) * q := by
  have hW0 : 0 < W := by linarith
  have hLi : 0 ≤ Li := by
    by_contra h; push Not at h
    have : W * Li / 4 < 0 := by
      have := mul_neg_of_pos_of_neg hW0 h; linarith
    linarith
  have a1 : e * τ ≤ e * (3 / 2 * Li * q) := mul_le_mul_of_nonneg_left hτ he
  have a2 : e ^ 2 * q ≤ 2 * e * q := mul_le_mul_of_nonneg_right (by nlinarith) hq
  have a3 : e * q ^ 2 / W ≤ e * q * (Li / 4) := by
    rw [div_le_iff₀ hW0]
    have : q * q ≤ q * (W * Li / 4) := mul_le_mul_of_nonneg_left hqW hq
    nlinarith
  have hw : 0 ≤ W⁻¹ ^ 2 * q := by positivity
  nlinarith

theorem drift_mean_lower {m q α W Li b Kr e : ℝ} (hq : 0 < q) (hW : 0 < W) (hb : 0 < b)
    (hα0 : 0 ≤ α) (hα : α ≤ Li / b) (hqW : q ≤ W * Li / 4)
    (hm : |m - q / (1 + α * q / W)| ≤ Kr * e * q)
    (hKe : Kr * e ≤ (1 + Li ^ 2 / (4 * b))⁻¹ / 2) :
    (1 + Li ^ 2 / (4 * b))⁻¹ * q / 2 ≤ m ∧
      (1 + Li ^ 2 / (4 * b))⁻¹ * q ≤ q / (1 + α * q / W) := by
  have hLi : 0 ≤ Li := by
    by_contra h; push Not at h
    have : W * Li / 4 < 0 := by have := mul_neg_of_pos_of_neg hW h; linarith
    linarith
  have hd0 : 0 < 1 + α * q / W := by positivity
  have hαq : α * q / W ≤ Li ^ 2 / (4 * b) := by
    rw [div_le_iff₀ hW]
    have h1 : α * q ≤ Li / b * (W * Li / 4) := mul_le_mul hα hqW hq.le (by positivity)
    have : Li / b * (W * Li / 4) = Li ^ 2 / (4 * b) * W := by field_simp
    linarith
  have hm0 : (1 + Li ^ 2 / (4 * b))⁻¹ * q ≤ q / (1 + α * q / W) := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hq.le hd0 (by linarith)
  refine ⟨?_, hm0⟩
  have := neg_abs_le (m - q / (1 + α * q / W))
  have h2 : Kr * e * q ≤ (1 + Li ^ 2 / (4 * b))⁻¹ / 2 * q := mul_le_mul_of_nonneg_right hKe hq.le
  linarith

theorem drift_inv_mean_le {m q α W Li b Kr e c₁ : ℝ} (hq : 0 < q) (hW : 0 < W)
    (hc₁ : 0 < c₁) (hα0 : 0 ≤ α) (hα : α ≤ Li / b)
    (hm : |m - q / (1 + α * q / W)| ≤ Kr * e * q) (hmlo : c₁ * q / 2 ≤ m)
    (hm0 : c₁ * q ≤ q / (1 + α * q / W)) :
    m⁻¹ ≤ q⁻¹ + Li / b * W⁻¹ + 2 * Kr / c₁ ^ 2 * (e / q) := by
  set m₀ := q / (1 + α * q / W)
  have hd0 : 0 < 1 + α * q / W := by positivity
  have hm₀ : 0 < m₀ := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hmlo
  have e1 : m₀⁻¹ = q⁻¹ + α * W⁻¹ := by simp only [m₀]; field_simp
  have e2 : m⁻¹ - m₀⁻¹ = (m₀ - m) / (m * m₀) := by field_simp
  have h3 : (m₀ - m) / (m * m₀) ≤ Kr * e * q / (c₁ * q / 2 * (c₁ * q)) := by
    have hnum : m₀ - m ≤ Kr * e * q := by
      have := neg_abs_le (m - m₀); linarith
    have hden : c₁ * q / 2 * (c₁ * q) ≤ m * m₀ :=
      mul_le_mul hmlo hm0 (by positivity) hmpos.le
    have hKq : 0 ≤ Kr * e * q := (abs_nonneg _).trans hm
    calc (m₀ - m) / (m * m₀) ≤ Kr * e * q / (m * m₀) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hKq (by positivity) hden
  have e3 : Kr * e * q / (c₁ * q / 2 * (c₁ * q)) = 2 * Kr / c₁ ^ 2 * (e / q) := by
    field_simp
  have h4 : α * W⁻¹ ≤ Li / b * W⁻¹ := mul_le_mul_of_nonneg_right hα (inv_nonneg.mpr hW.le)
  linarith

theorem drift_var_le {m q W C₂ c₁ : ℝ} (hq : 0 < q) (hW : 0 < W) (hc₁ : 0 < c₁)
    (hmlo : c₁ * q / 2 ≤ m) :
    2 * (C₂ * q / Real.sqrt W) ^ 2 / m ^ 3 ≤ 16 * C₂ ^ 2 / c₁ ^ 3 * (W * q)⁻¹ := by
  have hm : 0 < m := lt_of_lt_of_le (by positivity) hmlo
  have hs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have e1 : 2 * (C₂ * q / Real.sqrt W) ^ 2 = 2 * C₂ ^ 2 * q ^ 2 / W := by
    rw [div_pow, hs]; ring
  rw [e1]
  have hm3 : (c₁ * q / 2) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by positivity) hmlo 3
  calc 2 * C₂ ^ 2 * q ^ 2 / W / m ^ 3 ≤ 2 * C₂ ^ 2 * q ^ 2 / W / (c₁ * q / 2) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hm3
    _ = 16 * C₂ ^ 2 / c₁ ^ 3 * (W * q)⁻¹ := by field_simp; ring

theorem drift_tail_le {m q W CN c₁ A : ℝ} {N : ℕ} (hq : 0 < q) (hW : 1 ≤ W) (hc₁ : 0 < c₁)
    (hCN : 0 ≤ CN) (hmlo : c₁ * q / 2 ≤ m) (hAN : A ≤ N / 2) :
    (2 * (CN * q / Real.sqrt W) / m) ^ N ≤ (4 * CN / c₁) ^ N * W ^ (-A) := by
  have hW0 : 0 < W := by linarith
  have hm : 0 < m := lt_of_lt_of_le (by positivity) hmlo
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have h1 : 2 * (CN * q / Real.sqrt W) / m ≤ 4 * CN / c₁ * (Real.sqrt W)⁻¹ := by
    rw [div_le_iff₀ hm]
    have : 4 * CN / c₁ * (Real.sqrt W)⁻¹ * m ≥ 4 * CN / c₁ * (Real.sqrt W)⁻¹ * (c₁ * q / 2) :=
      mul_le_mul_of_nonneg_left hmlo (by positivity)
    have e : 4 * CN / c₁ * (Real.sqrt W)⁻¹ * (c₁ * q / 2) = 2 * (CN * q / Real.sqrt W) := by
      field_simp; ring
    linarith
  have h0 : 0 ≤ 2 * (CN * q / Real.sqrt W) / m := by positivity
  refine (pow_le_pow_left₀ h0 h1 N).trans ?_
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e : (Real.sqrt W)⁻¹ ^ N = W ^ (-((N : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, Real.inv_rpow (by positivity),
      ← Real.rpow_mul hW0.le, Real.rpow_neg hW0.le]
    congr 2; ring
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)

end BlockBand.Transmission.LawFinite
