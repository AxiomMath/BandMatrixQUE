module

public import BlockBand.Critical.RelativeVectors.ComparisonEvents
public import BlockBand.Critical.RelativeVectors.Scales

/-!
# Adding up the errors at the critical scales

At the critical scales (`t = N^{-1/500}`, `ℓ = ⌊N^{1-13/5000}⌋`, `w = ⌈N√t N^{2/10000}⌉`), for
`N ≥ 1`:
* `rmv_tlog_le`: `t(1 + log N) ≤ 1001 N^{-1/1000}`;
* `rmv_variation_le`: `t(N/ℓ)(t + w/N) ≤ 6 N^{-2/10000}`;
* `rmv_main_le`: the integrated diagonal and cross window terms
  `t(2r²k X_J + (kr)² C_comp √2 c̄) ≤ K_main N^{-1/5000}` (`K_main = rmvMainConst`);
* `rpow_le_rpow_left_one`, `rmv_N_div_ell_le`: auxiliary power and scale bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Real

variable {N : ℕ}

theorem rpow_le_rpow_left_one {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx h

theorem rmv_tlog_le (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(1 / 500 : ℝ)) * (1 + Real.log N) ≤ 1001 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log N ≤ (N : ℝ) ^ (1 / 1000 : ℝ) / (1 / 1000) :=
    Real.log_le_rpow_div hN0.le (by norm_num)
  have e : (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (1 / 1000 : ℝ) = (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hN0]; norm_num
  have h1 : (N : ℝ) ^ (-(1 / 500 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    rpow_le_rpow_left_one hN1 (by norm_num)
  have ht0 : 0 ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) := by positivity
  calc (N : ℝ) ^ (-(1 / 500 : ℝ)) * (1 + Real.log N)
      ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) * (1 + (N : ℝ) ^ (1 / 1000 : ℝ) / (1 / 1000)) := by gcongr
    _ = (N : ℝ) ^ (-(1 / 500 : ℝ)) + 1000 * ((N : ℝ) ^ (-(1 / 500 : ℝ)) *
          (N : ℝ) ^ (1 / 1000 : ℝ)) := by ring
    _ ≤ 1001 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by rw [e]; linarith

theorem rmv_N_div_ell_le (hN : 1 ≤ N) :
    (N : ℝ) / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ≤ 2 * (N : ℝ) ^ (13 / 5000 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hl, -⟩ := rmv_scale_le hN
  have hx0 : 0 < (N : ℝ) ^ (1 - 13 / 5000 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hfl : 0 < (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) := by linarith
  rw [div_le_iff₀ hfl]
  have e : (N : ℝ) ^ (13 / 5000 : ℝ) * (N : ℝ) ^ (1 - 13 / 5000 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  nlinarith [Real.rpow_pos_of_pos hN0 (13 / 5000 : ℝ)]

theorem rmv_variation_le (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(1 / 500 : ℝ)) * ((N : ℝ) / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) *
      ((N : ℝ) ^ (-(1 / 500 : ℝ)) + (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
        (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) / N)) ≤
      6 * (N : ℝ) ^ (-(2 / 10000 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw := rmv_w_div_le hN
  have hNl := rmv_N_div_ell_le hN
  have h1 : (N : ℝ) ^ (-(1 / 500 : ℝ)) ≤ (N : ℝ) ^ (-(8 / 10000 : ℝ)) :=
    rpow_le_rpow_left_one hN1 (by norm_num)
  have h2 : (1 : ℝ) / N ≤ (N : ℝ) ^ (-(8 / 10000 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact rpow_le_rpow_left_one hN1 (by norm_num)
  have hsum : (N : ℝ) ^ (-(1 / 500 : ℝ)) + (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
        (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) / N ≤ 3 * (N : ℝ) ^ (-(8 / 10000 : ℝ)) := by
    linarith
  have ht0 : 0 ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) := by positivity
  have hq0 : 0 ≤ (N : ℝ) / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) := by positivity
  have hs0 : 0 ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) + (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
        (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) / N := by positivity
  have e : (N : ℝ) ^ (-(1 / 500 : ℝ)) * ((2 * (N : ℝ) ^ (13 / 5000 : ℝ)) *
      (3 * (N : ℝ) ^ (-(8 / 10000 : ℝ)))) = 6 * (N : ℝ) ^ (-(2 / 10000 : ℝ)) := by
    have : (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (13 / 5000 : ℝ) *
        (N : ℝ) ^ (-(8 / 10000 : ℝ)) = (N : ℝ) ^ (-(2 / 10000 : ℝ)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
    rw [← this]; ring
  calc _ ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) * ((2 * (N : ℝ) ^ (13 / 5000 : ℝ)) *
        (3 * (N : ℝ) ^ (-(8 / 10000 : ℝ)))) := by gcongr
    _ = _ := e

/-- The constant of the main (diagonal and cross window) terms. -/
def rmvMainConst (r k : ℕ) (I R γ c₁ Csp Cd r₀ : ℝ) : ℝ :=
  2 * (r : ℝ) ^ 2 * k * (2 * (147 * I / c₁ ^ 2) * 4 + 2 * γ / c₁ * 1001 +
    4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) * 6 + 8 * γ / c₁ ^ 2 + (Cd + 64 / r₀ ^ 2)) +
    ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) * 4

/-- **The integrated diagonal and cross window terms** (from `2κ - α + ε - θ < 0`,
`κ - 3θ/2 + 2ε < 0`, `t log N → 0`). -/
theorem rmv_main_le (hN : 1 ≤ N) (r k : ℕ) {c r₀ s₀ v₀ I R c₁ Csp Cd : ℝ} (hI : 0 ≤ I)
    (hR : 0 ≤ R) (hγ : 0 ≤ gammaShiftConst c r₀ s₀ v₀) (hc₁ : 0 < c₁) (hCsp : 0 ≤ Csp)
    (hCd : 0 ≤ Cd) (hr₀ : 0 < r₀) :
    (N : ℝ) ^ (-(1 / 500 : ℝ)) * (2 * (r : ℝ) ^ 2 * k *
        diagXJ N c r₀ s₀ v₀ ((N : ℝ) ^ (-(1 / 500 : ℝ))) ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
          ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
          c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd +
      ((k : ℝ) * r) ^ 2 * (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) *
        (Real.sqrt 2 * ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2))))) ≤
      rmvMainConst r k I R (gammaShiftConst c r₀ s₀ v₀) c₁ Csp Cd r₀ *
        (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
  set γ := gammaShiftConst c r₀ s₀ v₀ with hγdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ)) with ht
  set L : ℝ := (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) with hL
  set W : ℝ := (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
    (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) with hW
  have hL0 : 0 < L := by
    obtain ⟨hl, -⟩ := rmv_scale_le hN
    have : 0 < (N : ℝ) ^ (1 - 13 / 5000 : ℝ) := Real.rpow_pos_of_pos hN0 _
    linarith
  have ht0 : 0 ≤ t := by positivity
  set T1 := t * ((N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) * N) / L ^ 2 with hT1
  set T4 := t * ((N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * N) / L ^ 2 with hT4
  have hT1b : T1 ≤ 4 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have e : (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) * N = (N : ℝ) ^ (2 - 1 / 100 + 1 / 10000 : ℝ) := by
      rw [← Real.rpow_add_one hN0.ne']
      norm_num
    rw [hT1, e]
    refine (rmv_fluctuation_term_le hN).trans ?_
    have : (N : ℝ) ^ (2 * (13 / 5000 : ℝ) - 1 / 100 + 1 / 10000 - 1 / 500) ≤
        (N : ℝ) ^ (-(1 / 5000 : ℝ)) := rpow_le_rpow_left_one hN1 (by norm_num)
    linarith
  have hT4b : T4 ≤ T1 := by
    rw [hT4, hT1]
    have : (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) := by
      rw [show (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) =
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add hN0]
      exact rpow_le_rpow_left_one hN1 (by norm_num)
    gcongr
  have hT2b : t * (1 + Real.log N) ≤ 1001 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    refine (rmv_tlog_le hN).trans ?_
    have : (N : ℝ) ^ (-(1 / 1000 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 5000 : ℝ)) :=
      rpow_le_rpow_left_one hN1 (by norm_num)
    linarith
  have hT3b : t * ((N : ℝ) / L * (t + W / N)) ≤ 6 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    refine (rmv_variation_le hN).trans (le_of_eq ?_)
    norm_num
  have htb : t ≤ (N : ℝ) ^ (-(1 / 5000 : ℝ)) := rpow_le_rpow_left_one hN1 (by norm_num)
  have hid : t * (2 * (r : ℝ) ^ 2 * k *
        diagXJ N c r₀ s₀ v₀ t ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
          ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
          c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd +
      ((k : ℝ) * r) ^ 2 * (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) *
        (Real.sqrt 2 * ((N : ℝ) / (c₁ ^ 2 * L ^ 2))))) =
      2 * (r : ℝ) ^ 2 * k * (2 * (147 * I / c₁ ^ 2) * T1 + 2 * γ / c₁ * (t * (1 + Real.log N)) +
        4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) * (t * ((N : ℝ) / L * (t + W / N))) +
        8 * γ / c₁ ^ 2 * t + (Cd + 64 / r₀ ^ 2) * t) +
      ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) * T4 := by
    rw [hT1, hT4]
    unfold diagXJ
    ring
  rw [hid]
  unfold rmvMainConst
  have hc1 : 0 < c₁ ^ 2 := by positivity
  have hk : (0 : ℝ) ≤ 2 * (r : ℝ) ^ 2 * k := by positivity
  have hK : 0 ≤ 4 / c₁ + Csp + 1 := by positivity
  have hP : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by positivity
  have h1 : 2 * (147 * I / c₁ ^ 2) * T1 ≤ 2 * (147 * I / c₁ ^ 2) * 4 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ 2 * (147 * I / c₁ ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hT1b h0
    linarith
  have h2 : 2 * γ / c₁ * (t * (1 + Real.log N)) ≤
      2 * γ / c₁ * 1001 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ 2 * γ / c₁ := by positivity
    have := mul_le_mul_of_nonneg_left hT2b h0
    linarith
  have h3 : 4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) * (t * ((N : ℝ) / L * (t + W / N))) ≤
      4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) * 6 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ 4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hT3b h0
    linarith
  have h4 : 8 * γ / c₁ ^ 2 * t ≤ 8 * γ / c₁ ^ 2 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ 8 * γ / c₁ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left htb h0
  have h5 : (Cd + 64 / r₀ ^ 2) * t ≤ (Cd + 64 / r₀ ^ 2) * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ Cd + 64 / r₀ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left htb h0
  have h6 : ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) * T4 ≤
      ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) * 4 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
    have h0 : 0 ≤ ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left (hT4b.trans hT1b) h0
    linarith
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
  have := mul_le_mul_of_nonneg_left hsum hk
  calc _ ≤ 2 * (r : ℝ) ^ 2 * k * (2 * (147 * I / c₁ ^ 2) * 4 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) +
          2 * γ / c₁ * 1001 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) +
          4 * γ / c₁ ^ 2 * (4 / c₁ + Csp + 1) * 6 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) +
          8 * γ / c₁ ^ 2 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) +
          (Cd + 64 / r₀ ^ 2) * (N : ℝ) ^ (-(1 / 5000 : ℝ))) +
        ((k : ℝ) * r) ^ 2 * (R * Real.sqrt 2 / c₁ ^ 2) * 4 * (N : ℝ) ^ (-(1 / 5000 : ℝ)) :=
        add_le_add this h6
    _ = _ := by ring

end BlockBand.Critical.RelativeVectors
