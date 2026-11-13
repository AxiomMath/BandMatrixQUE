module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real bookkeeping for the scalar weight

The displayed moment recursions are multiplied by `1 + K_pδ_{0,+}` with `K_p(1-ρ) > 2C_p`; its
predictable part absorbs `δ₀`.

* `lam_bound`: `Λ = 1 + nc + 2^n((c+σ₂)² + (c+σ_n)^n) ≤ 1 + Bc + 2^n(2σ₂² + 2^n s^{n-2}σ_n²)`;
* `weight_absorb`: `(1 + Kρδ + a₁/W)(1 + Lδ + a₂/W) + e/W ≤ (1 + Kδ)(1 + α/W)` when
  `L ≤ K(1-ρ)/2`, `ρLd ≤ (1-ρ)/2`, `δ ≤ d ≤ 1`, `W ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

theorem add_sq_le' (c σ : ℝ) : (c + σ) ^ 2 ≤ 2 * c ^ 2 + 2 * σ ^ 2 := by
  nlinarith [sq_nonneg (c - σ)]

theorem add_pow_le_two_pow {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) (n : ℕ) :
    (c + σ) ^ n ≤ 2 ^ n * (c ^ n + σ ^ n) := by
  rcases le_total c σ with h | h
  · have : c + σ ≤ 2 * σ := by linarith
    calc (c + σ) ^ n ≤ (2 * σ) ^ n := pow_le_pow_left₀ (by positivity) this n
      _ = 2 ^ n * σ ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (c ^ n + σ ^ n) := by
        have : 0 ≤ c ^ n := pow_nonneg hc n
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]
  · have : c + σ ≤ 2 * c := by linarith
    calc (c + σ) ^ n ≤ (2 * c) ^ n := pow_le_pow_left₀ (by positivity) this n
      _ = 2 ^ n * c ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (c ^ n + σ ^ n) := by
        have : 0 ≤ σ ^ n := pow_nonneg hσ n
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]

/-- **The one-step factor is `1 + O(c) + O(σ²)`.** -/
theorem lam_bound {c cm σ₂ σn s : ℝ} (hc : 0 ≤ c) (hcm : c ≤ cm) (hσn : 0 ≤ σn)
    (hs : σn ≤ s) {n : ℕ} (hn : 2 ≤ n) :
    1 + n * c + 2 ^ n * ((c + σ₂) ^ 2 + (c + σn) ^ n) ≤
      1 + (n + 2 ^ n * (2 * cm + 2 ^ n * cm ^ (n - 1))) * c +
        2 ^ n * (2 * σ₂ ^ 2 + 2 ^ n * s ^ (n - 2) * σn ^ 2) := by
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hcm0 : 0 ≤ cm := hc.trans hcm
  have e1 : (c + σ₂) ^ 2 ≤ 2 * cm * c + 2 * σ₂ ^ 2 := by
    have := add_sq_le' c σ₂
    nlinarith
  have e2 : (c + σn) ^ n ≤ 2 ^ n * (cm ^ (n - 1) * c + s ^ (n - 2) * σn ^ 2) := by
    refine (add_pow_le_two_pow hc hσn n).trans (mul_le_mul_of_nonneg_left ?_ h2n)
    have hcn : c ^ n ≤ cm ^ (n - 1) * c := by
      have : c ^ n = c ^ (n - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [this]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc hcm _) hc
    have hσ : σn ^ n ≤ s ^ (n - 2) * σn ^ 2 := by
      have : σn ^ n = σn ^ (n - 2) * σn ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hn]
      rw [this]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσn hs _) (sq_nonneg _)
    linarith
  have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) h2n
  nlinarith [mul_nonneg h2n (mul_nonneg h2n (mul_nonneg (pow_nonneg hcm0 (n - 1)) hc))]

/-- **The weight absorbs `δ₀`.** -/
theorem weight_absorb {K ρ L d δ a₁ a₂ e W : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hL : 0 ≤ L) (hKL : L ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1) (hρLd : ρ * L * d ≤ (1 - ρ) / 2)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ d) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (he : 0 ≤ e) (hW : 1 ≤ W) :
    (1 + K * ρ * δ + a₁ / W) * (1 + L * δ + a₂ / W) + e / W ≤
      (1 + K * δ) * (1 + (a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W) := by
  have hW0 : 0 < W := by linarith
  have hδ1 : δ ≤ 1 := hδ.trans hd1
  -- the `δ` terms
  have hlin : L * δ + K * ρ * δ + K * ρ * L * δ * δ ≤ K * δ := by
    have h1 : K * ρ * L * δ * δ ≤ K * ((1 - ρ) / 2) * δ := by
      have : ρ * L * δ ≤ (1 - ρ) / 2 :=
        (mul_le_mul_of_nonneg_left hδ (by positivity)).trans hρLd
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hK hδ0)
      nlinarith
    have h2 : L * δ ≤ K * (1 - ρ) / 2 * δ := mul_le_mul_of_nonneg_right hKL hδ0
    nlinarith
  -- the `1/W` terms
  have hinv : a₁ * a₂ / W ≤ a₁ * a₂ := div_le_self (by positivity) hW
  have hKρδ : K * ρ * δ * a₂ ≤ K * a₂ := by
    have : ρ * δ ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hK ha₂)]
  have hLδ : L * δ * a₁ ≤ L * a₁ := by nlinarith [mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hL ha₁)]
  have hrest : 0 ≤ K * δ * ((a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W) := by positivity
  have expand : (1 + K * ρ * δ + a₁ / W) * (1 + L * δ + a₂ / W) + e / W =
      1 + (L * δ + K * ρ * δ + K * ρ * L * δ * δ) +
        (a₂ + K * ρ * δ * a₂ + a₁ + L * δ * a₁ + a₁ * a₂ / W + e) / W := by
    field_simp; ring
  have expand2 : (1 + K * δ) * (1 + (a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W) =
      1 + K * δ + (a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W +
        K * δ * ((a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W) := by ring
  rw [expand, expand2]
  have hdiv : (a₂ + K * ρ * δ * a₂ + a₁ + L * δ * a₁ + a₁ * a₂ / W + e) / W ≤
      (a₁ + a₂ + K * a₂ + L * a₁ + a₁ * a₂ + e) / W :=
    div_le_div_of_nonneg_right (by linarith) hW0.le
  linarith

end BlockBand.SourceProcess.FullSource
