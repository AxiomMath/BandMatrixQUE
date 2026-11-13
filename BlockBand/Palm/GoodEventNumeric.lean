module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Good spectral event: scale bookkeeping for `N` large

Pure real-number estimates, no measure. With `h = N^{-1/100}`, `t = N^{-θ}`,
`ℓ = ⌊N^{1-κ}⌋` (`0 < θ`, `0 < κ < 1/100`):
* `scales_eventually`: every scale condition used by the deterministic assembly
  (`t ≤ s₀`, `t ≤ c/2`, `ℓ ≥ 1`, `16C₀Nh ≤ ℓ`, `64h/v₀² + 4h ≤ ℓ/N` and its two variants,
  `(1+1/c')ℓ/N ≤ r₀/8`, `3ℓ/(c'N) ≤ r₀/8`, `N^{-1/3} ≤ v₀/2, v₀⁻¹`, `16h/v₀² ≤ 1`, and the
  residual condition `h⁻² Cu N⁻¹ h⁻² ≤ 1` of the upper-count tail) holds for `N ≥ N₀`.
* `prob_eventually`: for a fixed moment order `p` (depending on `A, D`), the total failure
  probability of the union bound (two exponential terms, the time mesh `≤ 1 + Q h⁻⁴`, the space
  mesh `≤ 2((N^A + R₂)/h + 1) + 3`, the `p`-th moment tail and the `N^{-(D+1)}` local-law term)
  is at most `N^{-D}` for `N ≥ N₀`.
Helpers: `ev_poly_le` (`K N^α ≤ N^β` eventually for `α < β`), `ev_exp_le`
(`K N^b 2^{-N} ≤ N^c` eventually).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open Filter Topology

theorem ev_rpow_ge (K : ℝ) {a : ℝ} (ha : 0 < a) : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

theorem ev_rpow_neg_lt {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-a) < ε :=
  ((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hε)

/-- `K N^α ≤ N^β` for `N` large when `α < β`. -/
theorem ev_poly_le (K α β : ℝ) (h : α < β) :
    ∀ᶠ N : ℕ in atTop, K * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  filter_upwards [ev_rpow_ge K (sub_pos.2 h), eventually_ge_atTop 1] with N hK hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ β = (N : ℝ) ^ (β - α) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hN0, sub_add_cancel]
  rw [e]
  exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hN0.le _)

/-- `K N^b 2^{-N} ≤ N^c` for `N` large. -/
theorem ev_exp_le (K b c : ℝ) :
    ∀ᶠ N : ℕ in atTop, K * (N : ℝ) ^ b * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ c := by
  obtain ⟨k, hk⟩ := exists_nat_ge (b - c)
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hpos), eventually_ge_atTop 1] with N h1 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : (N : ℝ) ^ b = (N : ℝ) ^ c * (N : ℝ) ^ (b - c) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have e2 : (N : ℝ) ^ (b - c) ≤ (N : ℝ) ^ k := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 hk
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have e3 : K * (N : ℝ) ^ (b - c) * (1 / 2 : ℝ) ^ N ≤ 1 := by
    have hq : (N : ℝ) ^ k / 2 ^ N ≤ 1 / (|K| + 1) := h1.le
    have hx0 : 0 ≤ (N : ℝ) ^ (b - c) := Real.rpow_nonneg hN0.le _
    have hh0 : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    calc K * (N : ℝ) ^ (b - c) * (1 / 2 : ℝ) ^ N ≤ |K| * (N : ℝ) ^ (b - c) * (1 / 2 : ℝ) ^ N := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * (N : ℝ) ^ k * (1 / 2 : ℝ) ^ N := by gcongr
      _ = |K| * ((N : ℝ) ^ k / 2 ^ N) := by rw [one_div_pow]; ring
      _ ≤ |K| * (1 / (|K| + 1)) := by gcongr
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
  rw [e1]
  have hc0 : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg hN0.le _
  calc K * ((N : ℝ) ^ c * (N : ℝ) ^ (b - c)) * (1 / 2 : ℝ) ^ N =
        (N : ℝ) ^ c * (K * (N : ℝ) ^ (b - c) * (1 / 2 : ℝ) ^ N) := by ring
    _ ≤ (N : ℝ) ^ c * 1 := mul_le_mul_of_nonneg_left e3 hc0
    _ = (N : ℝ) ^ c := mul_one _

theorem inv_h_eq {N : ℕ} (hN0 : (0 : ℝ) < N) :
    ((N : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹ = (N : ℝ) ^ (1 / 100 : ℝ) := by
  rw [Real.rpow_neg hN0.le, inv_inv]

theorem inv_h_sq_eq {N : ℕ} (hN0 : (0 : ℝ) < N) :
    (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹ = (N : ℝ) ^ (2 / 100 : ℝ) := by
  rw [← inv_pow, inv_h_eq hN0, ← Real.rpow_mul_natCast hN0.le]
  norm_num

theorem base_eq {N : ℕ} (hN0 : (0 : ℝ) < N) :
    (N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹ = (N : ℝ) ^ (-(49 / 50 : ℝ)) := by
  rw [inv_h_sq_eq hN0, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
  norm_num

theorem scales_eventually {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hκ1 : κ < 1 / 100)
    {s₀ c C₀ v₀ r₀ c' Cu : ℝ} (hs₀ : 0 < s₀) (hc : 0 < c) (_hC₀ : 0 < C₀) (hv₀ : 0 < v₀)
    (hr₀ : 0 < r₀) (hc' : 0 < c') (_hCu : 0 < Cu) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      8 ≤ N ∧ (N : ℝ) ^ (-θ) ≤ s₀ ∧ (N : ℝ) ^ (-θ) ≤ c / 2 ∧ 1 ≤ ⌊(N : ℝ) ^ (1 - κ)⌋₊ ∧
      16 * C₀ * N * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) ∧
      64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤
        (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) / N ∧
      64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤
        (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) / (c' * N) ∧
      64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤
        3 / c' * (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) / N ∧
      (1 + 1 / c') * (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) / N ≤ r₀ / 8 ∧
      3 / c' * (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) / N ≤ r₀ / 8 ∧
      (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀ / 2 ∧ (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀⁻¹ ∧
      16 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 ≤ 1 ∧
      ((N : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹ * ((N : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹ *
        (Cu * ((N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹)) ≤ 1 := by
  have h1κ : 0 < 1 - κ := by linarith
  set W := 64 / v₀ ^ 2 + 4 with hW
  have hWpos : 0 < W := by positivity
  have hd1 : (0 : ℝ) < 1 + 1 / c' := by positivity
  have hd2 : (0 : ℝ) < 3 / c' := by positivity
  have hev : ∀ᶠ N : ℕ in atTop,
      8 ≤ N ∧ (N : ℝ) ^ (-θ) < s₀ ∧ (N : ℝ) ^ (-θ) < c / 2 ∧ 2 ≤ (N : ℝ) ^ (1 - κ) ∧
      32 * C₀ * (N : ℝ) ^ (1 + -(1 / 100 : ℝ)) ≤ (N : ℝ) ^ (1 - κ) ∧
      2 * W * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (N : ℝ) ^ (-κ) ∧
      2 * c' * W * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (N : ℝ) ^ (-κ) ∧
      2 * c' / 3 * W * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (N : ℝ) ^ (-κ) ∧
      (N : ℝ) ^ (-κ) < r₀ / 8 / (1 + 1 / c') ∧ (N : ℝ) ^ (-κ) < r₀ / 8 / (3 / c') ∧
      (N : ℝ) ^ (-(1 / 3 : ℝ)) < v₀ / 2 ∧ (N : ℝ) ^ (-(1 / 3 : ℝ)) < v₀⁻¹ ∧
      (N : ℝ) ^ (-(1 / 100 : ℝ)) < v₀ ^ 2 / 16 ∧
      Cu * (N : ℝ) ^ (-(24 / 25 : ℝ)) ≤ (N : ℝ) ^ (0 : ℝ) ∧ (1 : ℕ) ≤ N := by
    filter_upwards [eventually_ge_atTop 8, ev_rpow_neg_lt hs₀ hθ, ev_rpow_neg_lt (ε := c / 2) (by linarith) hθ,
      ev_rpow_ge 2 h1κ, ev_poly_le (32 * C₀) (1 + -(1 / 100 : ℝ)) (1 - κ) (by linarith),
      ev_poly_le (2 * W) (-(1 / 100 : ℝ)) (-κ) (by linarith),
      ev_poly_le (2 * c' * W) (-(1 / 100 : ℝ)) (-κ) (by linarith),
      ev_poly_le (2 * c' / 3 * W) (-(1 / 100 : ℝ)) (-κ) (by linarith),
      ev_rpow_neg_lt (by positivity : 0 < r₀ / 8 / (1 + 1 / c')) hκ,
      ev_rpow_neg_lt (by positivity : 0 < r₀ / 8 / (3 / c')) hκ,
      ev_rpow_neg_lt (by positivity : 0 < v₀ / 2) (by norm_num : (0 : ℝ) < 1 / 3),
      ev_rpow_neg_lt (by positivity : 0 < v₀⁻¹) (by norm_num : (0 : ℝ) < 1 / 3),
      ev_rpow_neg_lt (by positivity : 0 < v₀ ^ 2 / 16) (by norm_num : (0 : ℝ) < 1 / 100),
      ev_poly_le Cu (-(24 / 25 : ℝ)) 0 (by norm_num), eventually_ge_atTop 1]
      with N a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast a15
  set F := (N : ℝ) ^ (1 - κ) with hF
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hh
  set ℓ := (⌊F⌋₊ : ℝ) with hℓ
  have hFN : F = N * (N : ℝ) ^ (-κ) := by
    rw [hF, show (1 : ℝ) - κ = 1 + -κ by ring, Real.rpow_add hN0, Real.rpow_one]
  have hNh : (N : ℝ) * h = (N : ℝ) ^ (1 + -(1 / 100 : ℝ)) := by
    rw [Real.rpow_add hN0, Real.rpow_one]
  have hℓlow : F / 2 ≤ ℓ := by
    have := Nat.lt_floor_add_one F
    linarith
  have hℓup : ℓ ≤ F := Nat.floor_le (by linarith)
  have hlN : ℓ / N ≤ (N : ℝ) ^ (-κ) := by
    rw [div_le_iff₀ hN0]; linarith
  have hLHS : 64 * h / v₀ ^ 2 + 4 * h = W * h := by rw [hW]; ring
  have hκN : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg hN0.le _
  refine ⟨a1, a2.le, a3.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, a11.le, a12.le, ?_, ?_⟩
  · exact Nat.le_floor (by norm_num; linarith)
  · calc 16 * C₀ * N * h = 16 * C₀ * (N * h) := by ring
      _ = 16 * C₀ * (N : ℝ) ^ (1 + -(1 / 100 : ℝ)) := by rw [hNh]
      _ ≤ F / 2 := by linarith
      _ ≤ ℓ := hℓlow
  · rw [hLHS, le_div_iff₀ hN0]
    have : W * h * N ≤ (N : ℝ) ^ (-κ) * N / 2 := by nlinarith
    rw [mul_comm ((N : ℝ) ^ (-κ)), ← hFN] at this
    linarith
  · rw [hLHS, le_div_iff₀ (by positivity)]
    have : W * h * (c' * N) ≤ (N : ℝ) ^ (-κ) * N / 2 := by nlinarith
    rw [mul_comm ((N : ℝ) ^ (-κ)), ← hFN] at this
    linarith
  · rw [hLHS, mul_div_assoc, show 3 / c' * (ℓ / N) = ℓ / (c' / 3 * N) by field_simp,
      le_div_iff₀ (by positivity)]
    have : W * h * (c' / 3 * N) ≤ (N : ℝ) ^ (-κ) * N / 2 := by nlinarith
    rw [mul_comm ((N : ℝ) ^ (-κ)), ← hFN] at this
    linarith
  · rw [mul_div_assoc]
    have h9 : (1 + 1 / c') * (N : ℝ) ^ (-κ) < r₀ / 8 := by
      rw [lt_div_iff₀ hd1] at a9; linarith
    calc (1 + 1 / c') * (ℓ / N) ≤ (1 + 1 / c') * (N : ℝ) ^ (-κ) :=
          mul_le_mul_of_nonneg_left hlN hd1.le
      _ ≤ r₀ / 8 := h9.le
  · rw [mul_div_assoc]
    have h10 : 3 / c' * (N : ℝ) ^ (-κ) < r₀ / 8 := by
      rw [lt_div_iff₀ hd2] at a10; linarith
    calc 3 / c' * (ℓ / N) ≤ 3 / c' * (N : ℝ) ^ (-κ) :=
          mul_le_mul_of_nonneg_left hlN hd2.le
      _ ≤ r₀ / 8 := h10.le
  · rw [div_le_one (by positivity)]; linarith
  · rw [Real.rpow_zero] at a14
    calc h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹))
        = Cu * ((N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (-(49 / 50 : ℝ))) := by
          rw [hh, inv_h_eq hN0, base_eq hN0]; ring
      _ = Cu * (N : ℝ) ^ (-(24 / 25 : ℝ)) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
      _ ≤ 1 := a14

theorem prob_eventually (A D Cu R₂ Q : ℝ) (hCu : 0 < Cu) (hR₂ : 0 ≤ R₂) (hQ : 0 ≤ Q) :
    ∃ p : ℝ, 1 ≤ p ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (1 / 2 : ℝ) ^ N + (1 + Q * (((N : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹) ^ 4) *
        ((2 * (((N : ℝ) ^ A + R₂) / (N : ℝ) ^ (-(1 / 100 : ℝ)) + 1) + 3) *
            (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹)) ^ p +
          (N : ℝ) ^ (-(D + 1)) + (1 / 2 : ℝ) ^ N) ≤ (N : ℝ) ^ (-D) := by
  set A' := max A 0 with hA'
  set Dp := max D 0 with hDp
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  have hDp0 : 0 ≤ Dp := le_max_right _ _
  have hDDp : D ≤ Dp := le_max_left _ _
  set p := 2 * (Dp + A' + 3) with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  refine ⟨p, hp1, ?_⟩
  set Kp := (Cu * Real.sqrt p) ^ p with hKp
  have hKp0 : 0 ≤ Kp := Real.rpow_nonneg (by positivity) _
  have hev : ∀ᶠ N : ℕ in atTop,
      8 * (N : ℝ) ^ (0 : ℝ) * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) ∧
      4 * (1 + Q) * (7 + 2 * R₂) * Kp *
          (N : ℝ) ^ (4 / 100 + (A' + 1 / 100) + (-(49 / 50) * p)) ≤ (N : ℝ) ^ (-D) ∧
      4 * (1 + Q) * (N : ℝ) ^ (4 / 100 + -(D + 1)) ≤ (N : ℝ) ^ (-D) ∧
      4 * (1 + Q) * (N : ℝ) ^ (4 / 100 : ℝ) * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) ∧ (1 : ℕ) ≤ N := by
    filter_upwards [ev_exp_le 8 0 (-D),
      ev_poly_le (4 * (1 + Q) * (7 + 2 * R₂) * Kp) (4 / 100 + (A' + 1 / 100) + (-(49 / 50) * p))
        (-D) (by rw [hp]; linarith),
      ev_poly_le (4 * (1 + Q)) (4 / 100 + -(D + 1)) (-D) (by linarith),
      ev_exp_le (4 * (1 + Q)) (4 / 100) (-D), eventually_ge_atTop 1]
      with N b1 b2 b3 b4 b5
    exact ⟨b1, b2, b3, b4, b5⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := hN₀ N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast b5
  have hN0 : (0 : ℝ) < N := by linarith
  rw [Real.rpow_zero, mul_one] at b1
  -- identities
  have hX4 : (((N : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹) ^ 4 = (N : ℝ) ^ (4 / 100 : ℝ) := by
    rw [inv_h_eq hN0, ← Real.rpow_mul_natCast hN0.le]; norm_num
  have hdiv : ((N : ℝ) ^ A + R₂) / (N : ℝ) ^ (-(1 / 100 : ℝ)) =
      ((N : ℝ) ^ A + R₂) * (N : ℝ) ^ (1 / 100 : ℝ) := by
    rw [div_eq_mul_inv, inv_h_eq hN0]
  have hB : (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹)) ^ p =
      Kp * (N : ℝ) ^ (-(49 / 50) * p) := by
    rw [base_eq hN0, Real.mul_rpow (by positivity) (Real.rpow_nonneg hN0.le _),
      ← Real.rpow_mul hN0.le]
  rw [hX4, hdiv, hB]
  -- bounds
  set Y := (N : ℝ) ^ A' with hY
  set X := (N : ℝ) ^ (1 / 100 : ℝ) with hX
  set Z := (N : ℝ) ^ (4 / 100 : ℝ) with hZ
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 hA'0
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by norm_num)
  have hZ1 : 1 ≤ Z := Real.one_le_rpow hN1 (by norm_num)
  have hNA : (N : ℝ) ^ A ≤ Y := Real.rpow_le_rpow_of_exponent_le hN1 hAA'
  have hNA0 : 0 ≤ (N : ℝ) ^ A := Real.rpow_nonneg hN0.le _
  have hP : 1 + Q * Z ≤ (1 + Q) * Z := by nlinarith
  have hP0 : 0 ≤ 1 + Q * Z := by positivity
  have hM : 2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3 ≤ (7 + 2 * R₂) * (Y * X) := by
    have e1 : (N : ℝ) ^ A * X ≤ Y * X := mul_le_mul_of_nonneg_right hNA (by linarith)
    have e2 : R₂ * X ≤ R₂ * (Y * X) := by
      have : X ≤ Y * X := by nlinarith
      exact mul_le_mul_of_nonneg_left this hR₂
    have e3 : 1 ≤ Y * X := by nlinarith
    nlinarith
  have hM0 : 0 ≤ 2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3 := by positivity
  have hYX : Y * X = (N : ℝ) ^ (A' + 1 / 100) := by rw [hY, hX, Real.rpow_add hN0]
  have hEB0 : 0 ≤ (N : ℝ) ^ (-(49 / 50) * p) := Real.rpow_nonneg hN0.le _
  have hT1 : (1 + Q * Z) * ((2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3) *
      (Kp * (N : ℝ) ^ (-(49 / 50) * p))) ≤ (N : ℝ) ^ (-D) / 4 := by
    have hcomb : Z * ((N : ℝ) ^ (A' + 1 / 100) * (N : ℝ) ^ (-(49 / 50) * p)) =
        (N : ℝ) ^ (4 / 100 + (A' + 1 / 100) + (-(49 / 50) * p)) := by
      rw [hZ, Real.rpow_add hN0 (4 / 100 + (A' + 1 / 100)), Real.rpow_add hN0 (4 / 100)]; ring
    calc (1 + Q * Z) * ((2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3) *
          (Kp * (N : ℝ) ^ (-(49 / 50) * p)))
        ≤ ((1 + Q) * Z) * (((7 + 2 * R₂) * (Y * X)) * (Kp * (N : ℝ) ^ (-(49 / 50) * p))) := by
          apply mul_le_mul hP _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hM (by positivity)
      _ = (1 + Q) * (7 + 2 * R₂) * Kp *
          (Z * ((N : ℝ) ^ (A' + 1 / 100) * (N : ℝ) ^ (-(49 / 50) * p))) := by rw [hYX]; ring
      _ = (1 + Q) * (7 + 2 * R₂) * Kp *
          (N : ℝ) ^ (4 / 100 + (A' + 1 / 100) + (-(49 / 50) * p)) := by rw [hcomb]
      _ ≤ (N : ℝ) ^ (-D) / 4 := by linarith
  have hT2 : (1 + Q * Z) * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 4 := by
    have hc : Z * (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (4 / 100 + -(D + 1)) := by
      rw [hZ, Real.rpow_add hN0]
    calc (1 + Q * Z) * (N : ℝ) ^ (-(D + 1)) ≤ ((1 + Q) * Z) * (N : ℝ) ^ (-(D + 1)) :=
          mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hN0.le _)
      _ = (1 + Q) * (Z * (N : ℝ) ^ (-(D + 1))) := by ring
      _ = (1 + Q) * (N : ℝ) ^ (4 / 100 + -(D + 1)) := by rw [hc]
      _ ≤ (N : ℝ) ^ (-D) / 4 := by linarith
  have hT3 : (1 + Q * Z) * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) / 4 := by
    calc (1 + Q * Z) * (1 / 2 : ℝ) ^ N ≤ ((1 + Q) * Z) * (1 / 2 : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ ≤ (N : ℝ) ^ (-D) / 4 := by linarith
  have : (1 + Q * Z) * ((2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3) *
        (Kp * (N : ℝ) ^ (-(49 / 50) * p)) + (N : ℝ) ^ (-(D + 1)) + (1 / 2 : ℝ) ^ N) =
      (1 + Q * Z) * ((2 * (((N : ℝ) ^ A + R₂) * X + 1) + 3) *
        (Kp * (N : ℝ) ^ (-(49 / 50) * p))) + (1 + Q * Z) * (N : ℝ) ^ (-(D + 1)) +
        (1 + Q * Z) * (1 / 2 : ℝ) ^ N := by ring
  rw [this]
  linarith

end BlockBand.Palm.GoodEvent
