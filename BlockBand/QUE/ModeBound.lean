module

public import Mathlib

/-!
# The real Young absorption step for QUE Fourier modes

Young's inequality absorbs the square-root term of a mode estimate `(d/2) γ ≤ a + b√γ` into
`γ ≤ 4a/d + 4b²/d²`, and a lower bound on the mode separations makes the bound uniform over the
modes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE

/-- Young's inequality absorbs the square-root term with the exact loss
`4 a / d + 4 b² / d²`. No sign condition on `a` or `b` is needed. -/
theorem young_absorption {γ d a b : ℝ}
    (hγ : 0 ≤ γ) (hd : 0 < d)
    (h : d / 2 * γ ≤ a + b * Real.sqrt γ) :
    γ ≤ 4 * a / d + 4 * b ^ 2 / d ^ 2 := by
  have hsqrt := Real.sq_sqrt hγ
  have hscaled := mul_le_mul_of_nonneg_left h hd.le
  have hsquare := sq_nonneg (d * Real.sqrt γ - 2 * b)
  have hbound : d ^ 2 * γ ≤ 4 * a * d + 4 * b ^ 2 := by
    nlinarith
  have hden : 0 < d ^ 2 := sq_pos_of_pos hd
  have hquot : γ ≤ (4 * a * d + 4 * b ^ 2) / d ^ 2 := by
    apply (le_div_iff₀ hden).2
    nlinarith [hbound]
  calc
    γ ≤ (4 * a * d + 4 * b ^ 2) / d ^ 2 := hquot
    _ = 4 * a / d + 4 * b ^ 2 / d ^ 2 := by
      field_simp

/-- Absorption applied to the mode estimate with coefficients `a = A / W` and `b = B / q`, where
`q` is the positive angular-centre scale. -/
theorem mode_bound {γ d A B W q : ℝ}
    (hγ : 0 ≤ γ) (hd : 0 < d)
    (h : d / 2 * γ ≤ A / W + (B / q) * Real.sqrt γ) :
    γ ≤ 4 * (A / W) / d + 4 * (B / q) ^ 2 / d ^ 2 :=
  young_absorption hγ hd h

/-- A lower bound on every nonzero mode separation (`d_m ≥ 4/n` in use) makes the absorbed bound
uniform over the modes. -/
theorem uniform_mode_bound {γ d δ a b : ℝ}
    (hγ : 0 ≤ γ) (hδ : 0 < δ) (hδd : δ ≤ d) (ha : 0 ≤ a)
    (h : d / 2 * γ ≤ a + b * Real.sqrt γ) :
    γ ≤ 4 * a / δ + 4 * b ^ 2 / δ ^ 2 := by
  have hd : 0 < d := lt_of_lt_of_le hδ hδd
  calc
    γ ≤ 4 * a / d + 4 * b ^ 2 / d ^ 2 := young_absorption hγ hd h
    _ ≤ 4 * a / δ + 4 * b ^ 2 / δ ^ 2 := by
      gcongr

end BlockBand.QUE
