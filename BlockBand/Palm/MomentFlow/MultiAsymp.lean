module

public import BlockBand.Palm.MomentFlow.MultiFixedMain
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The scale arithmetic of the short flow

* `kappaR_le`: `κ_r ≤ Q n⁵` with an explicit `Q` (so `κ_r τ ≤ Q/n`);
* `multi_scales`: for `0 < ε ≤ 1/300` and every `D`, eventually in `N`: `a = c - τ > 0`, `ℓ ≥ 1`,
  and the scale hypotheses `P2`–`P7` of `multi_fixed`;
* `multi_scales_large`: for `ε > 1/300`, eventually `N ≤ N^ε ℓ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Filter Topology Real
open BlockBand.Palm.RelativeLocalization

/-- The constant of `kappaR_le`. -/
def kappaQ (r : ℕ) (r₀ c₁ C₁ : ℝ) : ℝ :=
  let W := weightConst
  let Kc := Real.exp (W * (2 * C₁))
  r * (2 * Kc * (W / (r₀ / 64) + 2 * (W + W ^ 2)) + 8 * W * 601 / c₁ + 2 * W / (r₀ / 64) +
      4 * (W + W ^ 2)) + 4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1)

theorem kappaQ_pos (r : ℕ) {r₀ c₁ C₁ : ℝ} (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) :
    0 ≤ kappaQ r r₀ c₁ C₁ := by
  unfold kappaQ
  have := weightConst_pos
  positivity

/-- **The rate bound** `κ_r ≤ Q n⁵`. -/
theorem kappaR_le {N ℓ r : ℕ} {r₀ c₁ C₁ n : ℝ} (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) (hn : 1 ≤ n)
    (hN : 1 ≤ (N : ℝ)) (hℓ : 0 < (ℓ : ℝ)) (hν : (N : ℝ) / ℓ ≤ 2 * n ^ 2)
    (hlog : Real.log N ≤ 600 * n) :
    kappaR N ℓ r r₀ c₁ C₁ ≤ kappaQ r r₀ c₁ C₁ * n ^ 5 := by
  have hW := weightConst_pos
  set W := weightConst with hWdef
  set ν : ℝ := (N : ℝ) / ℓ with hνdef
  have hNr : (0 : ℝ) < N := by linarith
  have hν0 : 0 ≤ ν := by positivity
  set R₀ : ℝ := r₀ / 64 with hR₀
  have hR₀p : 0 < R₀ := by positivity
  set Kc := Real.exp (W * (2 * C₁)) with hKc
  have hKc0 : 0 < Kc := Real.exp_pos _
  have hKeq : Real.exp (ν * W * (2 * C₁ * ℓ / N)) = Kc := by
    rw [hKc]; congr 1; rw [hνdef]; field_simp
  have hdeq : W / ((ℓ : ℝ) / N) = W * ν := by rw [hνdef]; field_simp
  have hLν : (ℓ : ℝ) / N * ν = 1 := by rw [hνdef]; field_simp
  have hn2 : n ^ 2 ≤ n ^ 5 := pow_le_pow_right₀ hn (by norm_num)
  have hn3 : n ^ 3 ≤ n ^ 5 := pow_le_pow_right₀ hn (by norm_num)
  have hn4 : n ^ 4 ≤ n ^ 5 := pow_le_pow_right₀ hn (by norm_num)
  have hn1 : 1 ≤ n ^ 5 := one_le_pow₀ hn
  have hν2 : ν ^ 2 ≤ 4 * n ^ 4 := by nlinarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN
  -- the four terms
  have T1 : 2 * ℓ * (ν * (W / R₀ + W / ((ℓ : ℝ) / N)) + ν ^ 2 * W ^ 2) * Kc / N ≤
      2 * Kc * (W / R₀ + 2 * (W + W ^ 2)) * n ^ 5 := by
    have e : 2 * ℓ * (ν * (W / R₀ + W / ((ℓ : ℝ) / N)) + ν ^ 2 * W ^ 2) * Kc / N =
        2 * Kc * (W / R₀ + ν * (W + W ^ 2)) := by
      rw [hdeq]
      have : (ℓ : ℝ) / N * (ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2) =
          W / R₀ + ν * (W + W ^ 2) := by
        have h1 : (ℓ : ℝ) / N * (ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2) =
            ((ℓ : ℝ) / N * ν) * (W / R₀ + ν * (W + W ^ 2)) := by ring
        rw [h1, hLν, one_mul]
      calc 2 * ℓ * (ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2) * Kc / N
          = 2 * Kc * ((ℓ : ℝ) / N * (ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2)) := by ring
        _ = _ := by rw [this]
    rw [e]
    have : W / R₀ + ν * (W + W ^ 2) ≤ (W / R₀ + 2 * (W + W ^ 2)) * n ^ 5 := by
      have h1 : ν * (W + W ^ 2) ≤ 2 * n ^ 2 * (W + W ^ 2) :=
        mul_le_mul_of_nonneg_right hν (by positivity)
      have h2 : W / R₀ ≤ W / R₀ * n ^ 5 := le_mul_of_one_le_right (by positivity) hn1
      nlinarith
    calc 2 * Kc * (W / R₀ + ν * (W + W ^ 2)) ≤ 2 * Kc * ((W / R₀ + 2 * (W + W ^ 2)) * n ^ 5) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have T2 : 2 * (ν * W) * (1 + Real.log N) / (c₁ / 2) ≤ 8 * W * 601 / c₁ * n ^ 5 := by
    have h1 : 1 + Real.log N ≤ 601 * n := by linarith
    have h2 : ν * W * (1 + Real.log N) ≤ 2 * n ^ 2 * W * (601 * n) := by
      gcongr
    have e : 2 * (ν * W) * (1 + Real.log N) / (c₁ / 2) =
        4 / c₁ * (ν * W * (1 + Real.log N)) := by
      field_simp; ring
    have e2 : 4 / c₁ * (2 * n ^ 2 * W * (601 * n)) = 8 * W * 601 / c₁ * n ^ 3 := by
      field_simp; ring
    rw [e]
    calc 4 / c₁ * (ν * W * (1 + Real.log N))
        ≤ 4 / c₁ * (2 * n ^ 2 * W * (601 * n)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 * W * 601 / c₁ * n ^ 3 := e2
      _ ≤ _ := mul_le_mul_of_nonneg_left hn3 (by positivity)
  have T3 : (ν * (W / R₀ + W / ((ℓ : ℝ) / N)) + ν ^ 2 * W ^ 2) / (2 * N) ≤
      (2 * W / R₀ + 4 * (W + W ^ 2)) * n ^ 5 := by
    rw [hdeq]
    have h0 : 0 ≤ ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2 := by positivity
    have h1 : (ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2) / (2 * N) ≤
        ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2 :=
      div_le_self h0 (by linarith)
    have h2 : ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2 = ν * (W / R₀) + ν ^ 2 * (W + W ^ 2) := by ring
    have h3 : ν * (W / R₀) ≤ 2 * n ^ 2 * (W / R₀) := mul_le_mul_of_nonneg_right hν (by positivity)
    have h4 : ν ^ 2 * (W + W ^ 2) ≤ 4 * n ^ 4 * (W + W ^ 2) :=
      mul_le_mul_of_nonneg_right hν2 (by positivity)
    have h5 : 2 * n ^ 2 * (W / R₀) ≤ 2 * W / R₀ * n ^ 5 := by
      have : 2 * n ^ 2 * (W / R₀) = 2 * W / R₀ * n ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hn2 (by positivity)
    have h6 : 4 * n ^ 4 * (W + W ^ 2) ≤ 4 * (W + W ^ 2) * n ^ 5 := by
      have : 4 * n ^ 4 * (W + W ^ 2) = 4 * (W + W ^ 2) * n ^ 4 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hn4 (by positivity)
    calc _ ≤ ν * (W / R₀ + W * ν) + ν ^ 2 * W ^ 2 := h1
      _ = _ := h2
      _ ≤ 2 * W / R₀ * n ^ 5 + 4 * (W + W ^ 2) * n ^ 5 := by linarith
      _ = _ := by ring
  have T4 : (r : ℝ) ^ 2 * ((ν * W) ^ 2 * (Kc ^ 2 + 1)) / (2 * N) ≤
      4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1) * n ^ 5 := by
    have h0 : 0 ≤ (r : ℝ) ^ 2 * ((ν * W) ^ 2 * (Kc ^ 2 + 1)) := by positivity
    have h1 := div_le_self h0 (show (1 : ℝ) ≤ 2 * N by linarith)
    have h2 : (r : ℝ) ^ 2 * ((ν * W) ^ 2 * (Kc ^ 2 + 1)) ≤
        (r : ℝ) ^ 2 * ((4 * n ^ 4) * W ^ 2 * (Kc ^ 2 + 1)) := by
      have : (ν * W) ^ 2 = ν ^ 2 * W ^ 2 := by ring
      rw [this]; gcongr
    have h3 : (r : ℝ) ^ 2 * ((4 * n ^ 4) * W ^ 2 * (Kc ^ 2 + 1)) ≤
        4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1) * n ^ 5 := by
      have : (r : ℝ) ^ 2 * ((4 * n ^ 4) * W ^ 2 * (Kc ^ 2 + 1)) =
          4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1) * n ^ 4 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hn4 (by positivity)
    linarith
  have hk : kappaR N ℓ r r₀ c₁ C₁ = r * (2 * ℓ * (ν * (W / R₀ + W / ((ℓ : ℝ) / N)) +
      ν ^ 2 * W ^ 2) * Real.exp (ν * W * (2 * C₁ * ℓ / N)) / N +
      2 * (ν * W) * (1 + Real.log N) / (c₁ / 2) +
      (ν * (W / R₀ + W / ((ℓ : ℝ) / N)) + ν ^ 2 * W ^ 2) / (2 * N)) +
      r ^ 2 * ((ν * W) ^ 2 * (Real.exp (ν * W * (2 * C₁ * ℓ / N)) ^ 2 + 1)) / (2 * N) := rfl
  have hq : kappaQ r r₀ c₁ C₁ = r * (2 * Kc * (W / R₀ + 2 * (W + W ^ 2)) + 8 * W * 601 / c₁ +
      2 * W / R₀ + 4 * (W + W ^ 2)) + 4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1) := rfl
  rw [hk, hq, hKeq]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hsum := add_le_add (add_le_add T1 T2) T3
  have h1 := mul_le_mul_of_nonneg_left hsum hr0
  have h2 : (r * (2 * Kc * (W / R₀ + 2 * (W + W ^ 2)) + 8 * W * 601 / c₁ +
      2 * W / R₀ + 4 * (W + W ^ 2)) + 4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1)) * n ^ 5 =
      r * (2 * Kc * (W / R₀ + 2 * (W + W ^ 2)) * n ^ 5 + 8 * W * 601 / c₁ * n ^ 5 +
        (2 * W / R₀ + 4 * (W + W ^ 2)) * n ^ 5) + 4 * r ^ 2 * W ^ 2 * (Kc ^ 2 + 1) * n ^ 5 := by
    ring
  rw [h2]
  linarith

/-!
### The variable `n = N^{1/600}`
-/

theorem rpow_600 {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : x ^ ((k : ℝ) / 600) = (x ^ ((1 : ℝ) / 600)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; ring

theorem p7_aux {rr P T A0 xD : ℝ} (hrr : 0 ≤ rr) (hP : 0 ≤ P) (hA0 : A0 = 3 * (rr * P))
    (hA0p : 0 < A0) (hxD : 0 ≤ xD) (h7 : T ≤ 1 / A0) : rr * P * T * xD ≤ xD / 3 := by
  have h1 : rr * P * T ≤ rr * P * (1 / A0) := mul_le_mul_of_nonneg_left h7 (mul_nonneg hrr hP)
  have h2 : rr * P * (1 / A0) ≤ 1 / 3 := by
    rw [hA0] at hA0p ⊢
    rcases eq_or_lt_of_le (mul_nonneg hrr hP) with h | h
    · rw [← h]; norm_num
    · rw [mul_one_div, div_le_div_iff₀ hA0p (by norm_num)]; linarith
  calc rr * P * T * xD ≤ 1 / 3 * xD := mul_le_mul_of_nonneg_right (h1.trans h2) hxD
    _ = xD / 3 := by ring

theorem p7_final (r : ℕ) {x ε D c₂ A0 sexp : ℝ} (hxp : 0 < x) (hε : 0 < ε)
    (hrr : 0 < (r : ℝ) ^ r) (hA0 : A0 = 3 * ((r : ℝ) ^ r * Real.exp (3 + r))) (hA0p : 0 < A0)
    (hsexp : sexp = (2 * r + D) / ε)
    (h7 : (x ^ ε) ^ sexp * Real.exp (-(c₂ / 2) * x ^ ε) ≤ 1 / A0) :
    x ^ r * ((r : ℝ) ^ r * x ^ r) * Real.exp (3 + r) * Real.exp (-(c₂ / 2 * x ^ ε)) ≤
      x ^ (-D) / 3 := by
  have hx0 : 0 ≤ x := hxp.le
  have hpow : (x ^ ε) ^ sexp = x ^ (2 * (r : ℝ) + D) := by
    rw [← Real.rpow_mul hx0]; congr 1; rw [hsexp]; field_simp [hε.ne']
  rw [hpow] at h7
  have e1 : x ^ (2 * (r : ℝ)) = (x ^ r) ^ 2 := by
    rw [← Real.rpow_natCast x r, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx0]
    congr 1; push_cast; ring
  have hxr : x ^ r * ((r : ℝ) ^ r * x ^ r) = (r : ℝ) ^ r * x ^ (2 * (r : ℝ)) := by
    rw [e1]; ring
  have hsplit : x ^ (2 * (r : ℝ)) = x ^ (2 * (r : ℝ) + D) * x ^ (-D) := by
    rw [← Real.rpow_add hxp]; congr 1; ring
  rw [hxr, hsplit]
  have hxD : 0 < x ^ (-D) := Real.rpow_pos_of_pos hxp _
  have h7' : x ^ (2 * (r : ℝ) + D) * Real.exp (-(c₂ / 2 * x ^ ε)) ≤ 1 / A0 := by
    simpa only [neg_mul] using h7
  have hP : 0 ≤ Real.exp (3 + r) := (Real.exp_pos _).le
  have hfin := p7_aux hrr.le hP hA0 hA0p hxD.le h7'
  calc (r : ℝ) ^ r * (x ^ (2 * (r : ℝ) + D) * x ^ (-D)) * Real.exp (3 + r) *
        Real.exp (-(c₂ / 2 * x ^ ε))
      = (r : ℝ) ^ r * Real.exp (3 + r) *
        (x ^ (2 * (r : ℝ) + D) * Real.exp (-(c₂ / 2 * x ^ ε))) * x ^ (-D) := by ring
    _ ≤ x ^ (-D) / 3 := hfin

/-- **The scales**, `0 < ε ≤ 1/300`. -/
theorem multi_scales (r : ℕ) {ε D C c₁ C₁ r₀ c c₂ : ℝ} (hε : 0 < ε) (hε3 : ε ≤ 1 / 300)
    (hC : 0 < C) (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) (hc : 0 < c) (hc₂ : 0 < c₂) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ N ∧ 0 < c - (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      1 ≤ ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ∧
      ((⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) : ℝ) / N ≤ r₀ / 32 ∧
      kappaR N ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ r r₀ c₁ C₁ * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 ∧
      (N : ℝ) / (⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) *
        (2 * C * Real.sqrt ((N : ℝ) ^ (-(1 / 100 : ℝ)))) ≤ 1 ∧
      (N : ℝ) / (⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 ∧
      (N : ℝ) ^ ε ≤ (N : ℝ) / (⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) ∧
      (N : ℝ) ^ r * ((r : ℝ) ^ r * (N : ℝ) ^ r) * Real.exp (3 + r) *
        Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) ≤ (N : ℝ) ^ (-D) / 3 := by
  set Q := kappaQ r r₀ c₁ C₁ with hQ
  have hQ0 : 0 ≤ Q := kappaQ_pos r hr₀ hc₁
  set M : ℝ := max (max (max 2 (1 / c + 1)) (max (32 / r₀) (4 * C))) (Q + 1) with hM
  -- `n → ∞`
  have hn_ev : ∀ᶠ N : ℕ in atTop, M ≤ (N : ℝ) ^ ((1 : ℝ) / 600) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 600)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M)
  -- P7
  set A0 : ℝ := 3 * ((r : ℝ) ^ r * Real.exp (3 + r)) with hA0
  have hrr : 0 < (r : ℝ) ^ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · positivity
  have hA0p : 0 < A0 := by positivity
  set sexp : ℝ := (2 * r + D) / ε with hsexp
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero sexp (c₂ / 2)
    (by positivity)).comp ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)
  have h7_ev : ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ ε) ^ sexp * Real.exp (-(c₂ / 2) * (N : ℝ) ^ ε) ≤
      1 / A0 := hlim.eventually (ge_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((hn_ev.and h7_ev).and (eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hnM, h7⟩, h2⟩ := hN₀ N hN
  set x : ℝ := (N : ℝ) with hxdef
  have hx2 : (2 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast h2
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  set n : ℝ := x ^ ((1 : ℝ) / 600) with hndef
  have hMn : M ≤ n := hnM
  have hn2 : 2 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hMn
  have hn1 : 1 ≤ n := by linarith
  have hnp : 0 < n := by linarith
  have hnc : 1 / c + 1 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hMn
  have hnr : 32 / r₀ ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hMn
  have hnC : 4 * C ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hMn
  have hnQ : Q + 1 ≤ n := le_trans (le_max_right _ _) hMn
  -- powers
  have hx600 : x = n ^ 600 := by
    have := rpow_600 hx0 600
    rw [show ((600 : ℕ) : ℝ) / 600 = 1 by norm_num, Real.rpow_one] at this
    exact this
  have hα : x ^ (1 - (1 / 100 : ℝ) / 3) = n ^ 598 := by
    rw [← rpow_600 hx0 598]; congr 1; norm_num
  have hτ : x ^ (-(1 / 100 : ℝ)) = 1 / n ^ 6 := by
    rw [Real.rpow_neg hx0, ← rpow_600 hx0 6, one_div]; norm_num
  have hsq : Real.sqrt (x ^ (-(1 / 100 : ℝ))) = 1 / n ^ 3 := by
    rw [hτ, show (1 : ℝ) / n ^ 6 = (1 / n ^ 3) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have h300 : x ^ ((1 : ℝ) / 300) = n ^ 2 := by
    rw [← rpow_600 hx0 2]; congr 1; norm_num
  have hlogx : Real.log x ≤ 600 * n := by
    have h1 : Real.log n = (1 / 600) * Real.log x := Real.log_rpow hxp _
    have h2 := Real.log_le_sub_one_of_pos hnp
    linarith
  -- the floor
  set ℓ := ⌊x ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ with hℓdef
  have hn598 : 2 ≤ n ^ 598 := le_trans hn2 (le_self_pow₀ hn1 (by norm_num))
  have hℓle : (ℓ : ℝ) ≤ n ^ 598 := by rw [hℓdef, hα]; exact Nat.floor_le (by positivity)
  have hℓge : n ^ 598 / 2 ≤ (ℓ : ℝ) := by
    have := Nat.lt_floor_add_one (n ^ 598)
    rw [hℓdef, hα]; linarith
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef, hα]; exact Nat.le_floor (by norm_num; linarith)
  have hℓp : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hνu : x / ℓ ≤ 2 * n ^ 2 := by
    rw [div_le_iff₀ hℓp, hx600]
    have : n ^ 600 = n ^ 2 * n ^ 598 := by ring
    rw [this]; nlinarith
  have hνl : n ^ 2 ≤ x / ℓ := by
    rw [le_div_iff₀ hℓp, hx600]
    have : n ^ 600 = n ^ 2 * n ^ 598 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hℓle (by positivity)
  refine ⟨h2, ?_, hℓ1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `a > 0`
    rw [hτ]
    have h6 : n ≤ n ^ 6 := le_self_pow₀ hn1 (by norm_num)
    have hc' : 1 / c < n ^ 6 := by linarith
    rw [div_lt_iff₀ hc] at hc'
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    linarith
  · -- P2
    have h1 : (ℓ : ℝ) / x ≤ 1 / n ^ 2 := by
      rw [div_le_div_iff₀ hxp (by positivity), hx600]
      have : n ^ 600 = n ^ 2 * n ^ 598 := by ring
      rw [this]; nlinarith
    have h2' : 1 / n ^ 2 ≤ r₀ / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 32 / r₀ ≤ n ^ 2 := le_trans hnr (le_self_pow₀ hn1 (by norm_num))
      rw [div_le_iff₀ hr₀] at this; linarith
    linarith
  · -- P3
    have hk := kappaR_le (r := r) (c₁ := c₁) (C₁ := C₁) hr₀ hc₁ hn1 (by linarith) hℓp hνu hlogx
    rw [hτ]
    have hk0 : kappaR N ℓ r r₀ c₁ C₁ * (1 / n ^ 6) ≤ Q * n ^ 5 * (1 / n ^ 6) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    have : Q * n ^ 5 * (1 / n ^ 6) = Q / n := by field_simp
    rw [this] at hk0
    have hQn : Q / n ≤ 1 := by rw [div_le_one hnp]; linarith
    linarith
  · -- P4
    rw [hsq]
    have h1 : x / ℓ * (2 * C * (1 / n ^ 3)) ≤ 2 * n ^ 2 * (2 * C * (1 / n ^ 3)) :=
      mul_le_mul_of_nonneg_right hνu (by positivity)
    have h2' : 2 * n ^ 2 * (2 * C * (1 / n ^ 3)) = 4 * C / n := by
      rw [show n ^ 3 = n ^ 2 * n by ring]; field_simp; ring
    have h3 : 4 * C / n ≤ 1 := by rw [div_le_one hnp]; exact hnC
    linarith
  · -- P5
    rw [hτ]
    have h1 : x / ℓ * (1 / n ^ 6) ≤ 2 * n ^ 2 * (1 / n ^ 6) :=
      mul_le_mul_of_nonneg_right hνu (by positivity)
    have h2' : 2 * n ^ 2 * (1 / n ^ 6) = 2 / n ^ 4 := by
      rw [show n ^ 6 = n ^ 2 * n ^ 4 by ring]; field_simp
    have h3 : 2 / n ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_trans hn2 (le_self_pow₀ hn1 (by norm_num))
    linarith
  · -- P6
    have h1 : x ^ ε ≤ x ^ ((1 : ℝ) / 300) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hε3
    rw [h300] at h1
    exact h1.trans hνl
  · -- P7
    exact p7_final r hxp hε hrr hA0 hA0p hsexp h7

/-- **Large `ε`**: eventually `N ≤ N^ε ℓ`, so no configuration is far. -/
theorem multi_scales_large {ε : ℝ} (hε : 1 / 300 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ≤ (N : ℝ) ^ ε * (⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε - 1 / 300)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hn_ev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 600) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 600)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((hlim.eventually (eventually_ge_atTop 2)).and
    (hn_ev.and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, hn, h2⟩ := hN₀ N hN
  have hx2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
  set x : ℝ := (N : ℝ)
  have hx2 : (2 : ℝ) ≤ x := hx2'
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  set n : ℝ := x ^ ((1 : ℝ) / 600)
  have hn1 : 1 ≤ n := by linarith
  have hα : x ^ (1 - (1 / 100 : ℝ) / 3) = n ^ 598 := by
    rw [← rpow_600 hx0 598]; congr 1; norm_num
  have hn598 : 2 ≤ n ^ 598 := le_trans hn (le_self_pow₀ hn1 (by norm_num))
  have hℓge : x ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤
      ((⌊x ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (x ^ (1 - (1 / 100 : ℝ) / 3))
    rw [hα] at this ⊢; linarith
  have hsplit : x ^ ε * x ^ (1 - (1 / 100 : ℝ) / 3) = x ^ (ε - 1 / 300) * x := by
    rw [← Real.rpow_add hxp]
    rw [show x ^ (ε - 1 / 300) * x = x ^ (ε - 1 / 300 + 1) by rw [Real.rpow_add hxp, Real.rpow_one]]
    congr 1; ring
  have hxε : 0 ≤ x ^ ε := Real.rpow_nonneg hx0 _
  calc x = 1 / 2 * (2 * x) := by ring
    _ ≤ 1 / 2 * (x ^ (ε - 1 / 300) * x) := by gcongr
    _ = x ^ ε * (x ^ (1 - (1 / 100 : ℝ) / 3) / 2) := by rw [← hsplit]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hℓge hxε

end BlockBand.Palm.MomentFlow
