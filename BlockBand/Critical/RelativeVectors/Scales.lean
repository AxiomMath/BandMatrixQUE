module

public import Mathlib

/-!
# The exponent bookkeeping

The relative-vector scales are `α = 1/100`, `θ = 1/500`, `κ = 13/5000`, `ε = 1/10000`,
`t = N^{-θ}`, `ℓ = ⌊N^{1-κ}⌋`. Deterministic.

* `rmv_fluctuation_exponent`, `rmv_variation_exponent`, `rmv_equilibration_exponent`: the
  three exponent identities `2κ - α + ε - θ = -0.0067`, `κ - 3θ/2 + 2ε = -0.0002`,
  `κ - θ = 0.0006`, and the smaller term `κ - 2θ < 0`.
* `rmv_scale_le`: for every `N ≥ 1`, `N^{1-κ}/2 ≤ ℓ ≤ N^{1-κ}`.
* `rmv_fluctuation_term_le`: `t N^{2-α+ε}/ℓ² ≤ 4 N^{2κ-α+ε-θ}` for `N ≥ 1` (the fluctuation and
  cross terms of the diagonal and cross relative error bounds, integrated over `[c - t, c]`).
* `rmv_equilibration_rate_ge`: `b₀ N t/(2ℓ) ≥ (b₀/2) N^{κ-θ}` for `N ≥ 1`, `b₀ ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

/-- Fluctuation and cross exponent: `2κ - α + ε - θ = -0.0067`. -/
theorem rmv_fluctuation_exponent :
    2 * (13 / 5000 : ℝ) - 1 / 100 + 1 / 10000 - 1 / 500 = -67 / 10000 := by norm_num

/-- Covariance-variation exponent: `κ - 3θ/2 + 2ε = -0.0002`. -/
theorem rmv_variation_exponent :
    (13 / 5000 : ℝ) - 3 / 2 * (1 / 500) + 2 * (1 / 10000) = -2 / 10000 := by norm_num

/-- Equilibration exponent: `N t/ℓ = N^{κ-θ}`, `κ - θ = 0.0006 > 0`. -/
theorem rmv_equilibration_exponent : (13 / 5000 : ℝ) - 1 / 500 = 6 / 10000 := by norm_num

/-- The smaller term `t (N/ℓ) t = N^{κ - 2θ}` also vanishes: `κ - 2θ < 0`. -/
theorem rmv_smaller_exponent : (13 / 5000 : ℝ) - 2 * (1 / 500) < 0 := by norm_num

/-- `N^{1-κ}/2 ≤ ℓ = ⌊N^{1-κ}⌋ ≤ N^{1-κ}` for `N ≥ 1`. -/
theorem rmv_scale_le {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - 13 / 5000 : ℝ) / 2 ≤ (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ∧
      (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (1 - 13 / 5000 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 13 / 5000 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  refine ⟨?_, Nat.floor_le (by linarith)⟩
  have h1 := Nat.lt_floor_add_one ((N : ℝ) ^ (1 - 13 / 5000 : ℝ))
  have h2 : (1 : ℝ) ≤ (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [Nat.floor_eq_zero] at h0
      linarith)
  linarith

/-- `t N^{2-α+ε}/ℓ² ≤ 4 N^{2κ-α+ε-θ}` for `N ≥ 1` (`t = N^{-θ}`, `ℓ = ⌊N^{1-κ}⌋`). -/
theorem rmv_fluctuation_term_le {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (2 - 1 / 100 + 1 / 10000 : ℝ) /
        (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2 ≤
      4 * (N : ℝ) ^ (2 * (13 / 5000 : ℝ) - 1 / 100 + 1 / 10000 - 1 / 500) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hl, -⟩ := rmv_scale_le hN
  set x := (N : ℝ) ^ (1 - 13 / 5000 : ℝ) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hl0 : 0 < x / 2 := by positivity
  have hsq : (x / 2) ^ 2 ≤ (⌊x⌋₊ : ℝ) ^ 2 := pow_le_pow_left₀ hl0.le hl 2
  have hnum : 0 ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (2 - 1 / 100 + 1 / 10000 : ℝ) := by
    positivity
  calc (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (2 - 1 / 100 + 1 / 10000 : ℝ) / (⌊x⌋₊ : ℝ) ^ 2
      ≤ (N : ℝ) ^ (-(1 / 500 : ℝ)) * (N : ℝ) ^ (2 - 1 / 100 + 1 / 10000 : ℝ) / (x / 2) ^ 2 :=
        div_le_div_of_nonneg_left hnum (by positivity) hsq
    _ = 4 * (N : ℝ) ^ (2 * (13 / 5000 : ℝ) - 1 / 100 + 1 / 10000 - 1 / 500) := by
        rw [div_pow, hxdef, ← Real.rpow_natCast ((N : ℝ) ^ (1 - 13 / 5000 : ℝ)) 2,
          ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        have h2 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
        rw [h2]
        have hpos : (0 : ℝ) < (N : ℝ) ^ ((1 - 13 / 5000 : ℝ) * ((2 : ℕ) : ℝ)) :=
          Real.rpow_pos_of_pos hN0 _
        field_simp
        rw [← Real.rpow_add hN0]
        norm_num

/-- Equilibration rate: `b₀ N t/(2ℓ) ≥ (b₀/2) N^{κ-θ}` for `N ≥ 1`, `b₀ ≥ 0`. -/
theorem rmv_equilibration_rate_ge {N : ℕ} (hN : 1 ≤ N) {b₀ : ℝ} (hb : 0 ≤ b₀) :
    b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) ≤
      b₀ * N * (N : ℝ) ^ (-(1 / 500 : ℝ)) / (2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hl, hu⟩ := rmv_scale_le hN
  set x := (N : ℝ) ^ (1 - 13 / 5000 : ℝ) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hfl : 0 < (⌊x⌋₊ : ℝ) := by linarith
  have hkey : (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) * x = N * (N : ℝ) ^ (-(1 / 500 : ℝ)) := by
    rw [hxdef, ← Real.rpow_add hN0]
    have h1 : (N : ℝ) * (N : ℝ) ^ (-(1 / 500 : ℝ)) = (N : ℝ) ^ ((1 : ℝ) + -(1 / 500 : ℝ)) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [h1]
    norm_num
  rw [le_div_iff₀ (by positivity)]
  have hy : 0 ≤ (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) := by positivity
  calc b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) * (2 * (⌊x⌋₊ : ℝ))
      ≤ b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) * (2 * x) := by
        gcongr
    _ = b₀ * (N * (N : ℝ) ^ (-(1 / 500 : ℝ))) := by rw [← hkey]; ring
    _ = b₀ * N * (N : ℝ) ^ (-(1 / 500 : ℝ)) := by ring

end BlockBand.Critical.RelativeVectors
