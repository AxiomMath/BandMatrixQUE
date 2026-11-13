module

public import BlockBand.Prelude

/-!
# Positive longitudinal coefficient in signed angular elimination

If `u₂ = s + a u₁ - (a²/4 + y²) u₀`, then
`1 - (u₂ - u₁²/u₀)/s = (u₀/s)((u₁/u₀ - a/2)² + y²)`, which is positive for `s, u₀, y > 0`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Angular

/-- Exact completion of the angular longitudinal coefficient into a positive square. -/
theorem longitudinal_coefficient_identity (s u₀ u₁ u₂ a y : ℝ)
    (hs : s ≠ 0) (hu : u₀ ≠ 0)
    (href : u₂ = s + a * u₁ - (a ^ 2 / 4 + y ^ 2) * u₀) :
    1 - (u₂ - u₁ ^ 2 / u₀) / s =
      u₀ / s * ((u₁ / u₀ - a / 2) ^ 2 + y ^ 2) := by
  rw [href]
  field_simp
  ring

/-- Positive imaginary height prevents a zero longitudinal denominator. -/
theorem longitudinal_coefficient_pos (s u₀ u₁ u₂ a y : ℝ)
    (hs : 0 < s) (hu : 0 < u₀) (hy : 0 < y)
    (href : u₂ = s + a * u₁ - (a ^ 2 / 4 + y ^ 2) * u₀) :
    0 < 1 - (u₂ - u₁ ^ 2 / u₀) / s := by
  rw [longitudinal_coefficient_identity s u₀ u₁ u₂ a y hs.ne' hu.ne' href]
  exact mul_pos (div_pos hu hs) (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy))

end BlockBand.Angular
