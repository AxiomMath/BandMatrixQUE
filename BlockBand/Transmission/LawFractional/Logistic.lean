module

public import BlockBand.Transmission.FractionalBulk.Logistic

/-!
# Rescaled discrete logistic comparison

**`logistic_scaled`**: if `y ≥ 0`, `y_{r₀+m+1} ≤ y_{r₀+m} - a y_{r₀+m}² + F` for `m < n`
(`a > 0`, `F ≥ 0`) and `M > 0` satisfies `F ≤ a M²`, then for `1 ≤ m ≤ n`,
`y_{r₀+m} ≤ max(2M + F, 2/(am))`.

This is `FractionalBulk.logistic_bound` applied to `z = y/M`. Its threshold is
`max(1, 2F/a)`, which is linear in the forcing. With `M ≈ √(F/a)`, the rescaled threshold is
the equilibrium `√(F/a)`. A forcing `F ≍ 1 + t⁻²` then gives the bound `C_p(1 + t⁻¹)` of the paper.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

/-- **Rescaled logistic comparison.** -/
theorem logistic_scaled {y : ℕ → ℝ} {a F M : ℝ} (ha : 0 < a) (hF : 0 ≤ F) (hM : 0 < M)
    (hMF : F ≤ a * M ^ 2) (r₀ n : ℕ) (hy : ∀ m, 0 ≤ y (r₀ + m))
    (hrec : ∀ m, m < n → y (r₀ + m + 1) ≤ y (r₀ + m) - a * y (r₀ + m) ^ 2 + F) :
    ∀ m, 1 ≤ m → m ≤ n → y (r₀ + m) ≤ max (2 * M + F) (2 / (a * m)) := by
  have hz := FractionalBulk.logistic_bound (y := fun r => y r / M) (a := a * M) (K := F / M)
    (by positivity) (by positivity) r₀ n (fun m => div_nonneg (hy m) hM.le) (fun m hm => by
      have h := hrec m hm
      have e : y (r₀ + m) / M - a * M * (y (r₀ + m) / M) ^ 2 + F / M =
          (y (r₀ + m) - a * y (r₀ + m) ^ 2 + F) / M := by field_simp
      rw [e]
      exact div_le_div_of_nonneg_right h hM.le)
  intro m hm1 hmn
  have h := hz m hm1 hmn
  have h2 : 2 * (F / M) / (a * M) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : F / M ≤ a * M := by rw [div_le_iff₀ hM]; nlinarith
    linarith
  have h1 : max 1 (2 * (F / M) / (a * M)) ≤ 2 := max_le (by norm_num) h2
  have h3 : y (r₀ + m) / M ≤ max (2 + F / M) (2 / (a * M * m)) :=
    h.trans (max_le_max (by linarith) le_rfl)
  rw [div_le_iff₀ hM] at h3
  refine h3.trans (le_of_eq ?_)
  rw [max_mul_of_nonneg _ _ hM.le]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  congr 1
  · field_simp
  · field_simp

end BlockBand.Transmission.LawFractional
