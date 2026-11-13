module

public import BlockBand.Palm.MomentFlow.MultiAsymp

/-!
# Column form: the rate of the reciprocal weight at the short-flow scales

The rate `kappaCol` of the reciprocal matching weight, and the scale bound `kappaCol · τ ≤ 1` at
`ℓ = ⌊N^{1-1/300}⌋`, `τ = N^{-1/100}` for large `N` (`multi_scales_col`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Filter Topology Real
open BlockBand.Palm.RelativeLocalization

/-- The rate of the reciprocal matching weight at the short-flow scales. -/
def kappaCol (N ℓ r : ℕ) (r₀ c₁ C₁ : ℝ) : ℝ :=
  let ν : ℝ := (N : ℝ) / ℓ
  kappaR N ℓ r r₀ c₁ C₁ +
    r * (2 * ℓ + r) * (ν * weightConst) ^ 2 * Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 3 /
      N + r ^ 2 * (ν * weightConst) ^ 2 / N

theorem kappaCol_le {N ℓ r : ℕ} {r₀ c₁ C₁ n : ℝ} (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) (hn : 1 ≤ n)
    (hN : 1 ≤ (N : ℝ)) (hℓ : 0 < (ℓ : ℝ)) (hrℓ : (r : ℝ) ≤ ℓ) (_hℓN : (ℓ : ℝ) ≤ N)
    (hν : (N : ℝ) / ℓ ≤ 2 * n ^ 2) (hlog : Real.log N ≤ 600 * n) :
    kappaCol N ℓ r r₀ c₁ C₁ ≤ (kappaQ r r₀ c₁ C₁ +
      6 * r * weightConst ^ 2 * Real.exp (weightConst * (2 * C₁)) ^ 3 +
      2 * r ^ 2 * weightConst ^ 2) * n ^ 5 := by
  have hk := kappaR_le (r := r) (C₁ := C₁) hr₀ hc₁ hn hN hℓ hν hlog
  have hW := weightConst_pos
  set W := weightConst
  set ν : ℝ := (N : ℝ) / ℓ with hνdef
  have hNr : (0 : ℝ) < N := by linarith
  have hν0 : 0 ≤ ν := by positivity
  set Kc := Real.exp (W * (2 * C₁)) with hKc
  have hKeq : Real.exp (ν * W * (2 * C₁ * ℓ / N)) = Kc := by
    rw [hKc]; congr 1; rw [hνdef]; field_simp
  have hLν : (ℓ : ℝ) / N * ν = 1 := by rw [hνdef]; field_simp
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    have : 0 < ℓ := by exact_mod_cast hℓ
    exact_mod_cast this
  have hν1 : ν ≤ N := by rw [hνdef, div_le_iff₀ hℓ]; nlinarith
  have hn2 : n ^ 2 ≤ n ^ 5 := pow_le_pow_right₀ hn (by norm_num)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have e : kappaCol N ℓ r r₀ c₁ C₁ = kappaR N ℓ r r₀ c₁ C₁ +
      r * (2 * ℓ + r) * (ν * W) ^ 2 * Kc ^ 3 / N + r ^ 2 * (ν * W) ^ 2 / N := by
    unfold kappaCol; rw [← hKeq]
  rw [e]
  have t1 : r * (2 * ℓ + r) * (ν * W) ^ 2 * Kc ^ 3 / N ≤ 6 * r * W ^ 2 * Kc ^ 3 * n ^ 5 := by
    have h1 : (2 * (ℓ : ℝ) + r) ≤ 3 * ℓ := by linarith
    have h2 : r * (2 * ℓ + r) * (ν * W) ^ 2 * Kc ^ 3 / N ≤
        r * (3 * ℓ) * (ν * W) ^ 2 * Kc ^ 3 / N := by gcongr
    have h3 : r * (3 * ℓ) * (ν * W) ^ 2 * Kc ^ 3 / N = 3 * r * W ^ 2 * Kc ^ 3 * ν *
        ((ℓ : ℝ) / N * ν) := by field_simp
    rw [hLν, mul_one] at h3
    have h4 : 3 * r * W ^ 2 * Kc ^ 3 * ν ≤ 3 * r * W ^ 2 * Kc ^ 3 * (2 * n ^ 2) :=
      mul_le_mul_of_nonneg_left hν (by positivity)
    have h5 : 3 * r * W ^ 2 * Kc ^ 3 * (2 * n ^ 2) ≤ 6 * r * W ^ 2 * Kc ^ 3 * n ^ 5 := by
      have : 3 * r * W ^ 2 * Kc ^ 3 * (2 * n ^ 2) = 6 * r * W ^ 2 * Kc ^ 3 * n ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hn2 (by positivity)
    linarith
  have t2 : (r : ℝ) ^ 2 * (ν * W) ^ 2 / N ≤ 2 * r ^ 2 * W ^ 2 * n ^ 5 := by
    have h1 : (r : ℝ) ^ 2 * (ν * W) ^ 2 / N ≤ r ^ 2 * W ^ 2 * ν := by
      rw [div_le_iff₀ hNr]
      have : (r : ℝ) ^ 2 * (ν * W) ^ 2 = r ^ 2 * W ^ 2 * ν * ν := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hν1 (by positivity)
    have h2 : (r : ℝ) ^ 2 * W ^ 2 * ν ≤ r ^ 2 * W ^ 2 * (2 * n ^ 2) :=
      mul_le_mul_of_nonneg_left hν (by positivity)
    have h3 : (r : ℝ) ^ 2 * W ^ 2 * (2 * n ^ 2) ≤ 2 * r ^ 2 * W ^ 2 * n ^ 5 := by
      have : (r : ℝ) ^ 2 * W ^ 2 * (2 * n ^ 2) = 2 * r ^ 2 * W ^ 2 * n ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hn2 (by positivity)
    linarith
  have : (kappaQ r r₀ c₁ C₁ + 6 * r * W ^ 2 * Kc ^ 3 + 2 * r ^ 2 * W ^ 2) * n ^ 5 =
      kappaQ r r₀ c₁ C₁ * n ^ 5 + 6 * r * W ^ 2 * Kc ^ 3 * n ^ 5 + 2 * r ^ 2 * W ^ 2 * n ^ 5 := by
    ring
  rw [this]
  linarith

/-- **Eventually `kappaCol τ ≤ 1`.** -/
theorem multi_scales_col (r : ℕ) {c₁ C₁ r₀ : ℝ} (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      kappaCol N ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ r r₀ c₁ C₁ *
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := by
  set Q := kappaQ r r₀ c₁ C₁ + 6 * r * weightConst ^ 2 *
    Real.exp (weightConst * (2 * C₁)) ^ 3 + 2 * r ^ 2 * weightConst ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by
    have := kappaQ_pos r (C₁ := C₁) hr₀ hc₁; have := weightConst_pos; positivity
  set M : ℝ := max (max 2 ((r : ℝ) + 2)) (Q + 1) with hM
  have hn_ev : ∀ᶠ N : ℕ in atTop, M ≤ (N : ℝ) ^ ((1 : ℝ) / 600) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 600)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hn_ev.and (eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hnM, h2⟩ := hN₀ N hN
  have hx2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
  set x : ℝ := (N : ℝ) with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  set n : ℝ := x ^ ((1 : ℝ) / 600) with hndef
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnM
  have hnr : (r : ℝ) + 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnM
  have hnQ : Q + 1 ≤ n := le_trans (le_max_right _ _) hnM
  have hn1 : 1 ≤ n := by linarith
  have hnp : 0 < n := by linarith
  have hx600 : x = n ^ 600 := by
    have := rpow_600 hx0 600
    rw [show ((600 : ℕ) : ℝ) / 600 = 1 by norm_num, Real.rpow_one] at this
    exact this
  have hα : x ^ (1 - (1 / 100 : ℝ) / 3) = n ^ 598 := by
    rw [← rpow_600 hx0 598]; congr 1; norm_num
  have hτ : x ^ (-(1 / 100 : ℝ)) = 1 / n ^ 6 := by
    rw [Real.rpow_neg hx0, ← rpow_600 hx0 6, one_div]; norm_num
  have hlogx : Real.log x ≤ 600 * n := by
    have h1 : Real.log n = (1 / 600) * Real.log x := Real.log_rpow hxp _
    have h2 := Real.log_le_sub_one_of_pos hnp
    linarith
  set ℓ := ⌊x ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ with hℓdef
  have hle598 : n ≤ n ^ 598 := le_self_pow₀ hn1 (by norm_num)
  have hℓle : (ℓ : ℝ) ≤ n ^ 598 := by rw [hℓdef, hα]; exact Nat.floor_le (by positivity)
  have hℓge : n ^ 598 / 2 ≤ (ℓ : ℝ) := by
    have := Nat.lt_floor_add_one (n ^ 598)
    rw [hℓdef, hα]
    have h598 : 2 ≤ n ^ 598 := le_trans hn2 hle598
    linarith
  have hℓp : (0 : ℝ) < ℓ := by
    have : (0 : ℝ) < n ^ 598 / 2 := by positivity
    linarith
  have hνu : x / ℓ ≤ 2 * n ^ 2 := by
    rw [div_le_iff₀ hℓp, hx600]
    have : n ^ 600 = n ^ 2 * n ^ 598 := by ring
    rw [this]; nlinarith
  have hrℓ : (r : ℝ) ≤ ℓ := by
    have h1 : n ≤ n ^ 598 / 2 := by
      have : 2 * n ≤ n ^ 598 := by
        have h3 : n ^ 2 ≤ n ^ 598 := pow_le_pow_right₀ hn1 (by norm_num)
        nlinarith
      linarith
    linarith
  have hℓN : (ℓ : ℝ) ≤ x := by
    rw [hx600]
    exact hℓle.trans (pow_le_pow_right₀ hn1 (by norm_num))
  have hk := kappaCol_le (r := r) (c₁ := c₁) (C₁ := C₁) hr₀ hc₁ hn1 (by linarith) hℓp hrℓ hℓN hνu
    hlogx
  rw [hτ]
  have hk0 : kappaCol N ℓ r r₀ c₁ C₁ * (1 / n ^ 6) ≤ Q * n ^ 5 * (1 / n ^ 6) :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  have : Q * n ^ 5 * (1 / n ^ 6) = Q / n := by field_simp
  rw [this] at hk0
  have hQn : Q / n ≤ 1 := by rw [div_le_one hnp]; linarith
  linarith

end BlockBand.Palm.MomentFlow
