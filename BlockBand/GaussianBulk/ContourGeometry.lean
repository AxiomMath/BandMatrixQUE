module

public import Mathlib

/-!
# Scalar contour geometry for the external-source sine kernel

Deterministic real inequalities used in the steepest-descent analysis of the external-source
sine-kernel theorem: transversal crossing of a graph with a vertical line and the curvature
bounds at the saddle. No probability measure is involved. In applications `a = x-x₀`,
`b = v-y₀`, `s = y(x)-y₀`, with a uniform graph slope bound.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.GaussianBulk

/-- A graph with slope bound `L` crosses a vertical line transversally.
This is a squared-distance inequality valid for every real local coordinate.
It provides a concrete coefficient `2*(1+L²)`, independent of dimension,
deformation spectrum and microscopic spectral tests. -/
theorem transverse_distance_sq (a b s L : ℝ)
    (hs : |s| ≤ L * |a|) :
    a ^ 2 + b ^ 2 ≤ 2 * (1 + L ^ 2) * (a ^ 2 + (b - s) ^ 2) := by
  have hs2 : s ^ 2 ≤ L ^ 2 * a ^ 2 := by
    calc
      s ^ 2 = |s| * |s| := by rw [abs_mul_abs_self, pow_two]
      _ ≤ (L * |a|) * (L * |a|) := mul_self_le_mul_self (abs_nonneg s) hs
      _ = L ^ 2 * a ^ 2 := by rw [← pow_two, mul_pow, sq_abs]
  have hdiff := sq_nonneg (b - 2 * s)
  have ha := sq_nonneg a
  have hd := sq_nonneg (b - s)
  have hLd : 0 ≤ L ^ 2 * (b - s) ^ 2 := mul_nonneg (sq_nonneg L) hd
  nlinarith

/-- The finite level equation and Jensen lower bound give the
strict curvature `ψ' = 2t(y²B+A₁²/B) ≥ 2y²/t`.
No differentiation or construction of the level graph is asserted here. -/
theorem horizontal_curvature_lower (t y B A₁ : ℝ) (ht : 0 < t)
    (hB : 0 < B) (hJensen : 1 / t ^ 2 ≤ B) :
    2 * y ^ 2 / t ≤ 2 * t * (y ^ 2 * B + A₁ ^ 2 / B) := by
  have hA : 0 ≤ A₁ ^ 2 / B := div_nonneg (sq_nonneg A₁) (le_of_lt hB)
  have hscale := mul_le_mul_of_nonneg_left hJensen (sq_nonneg y)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have heq : 2 * t * (y ^ 2 * (1 / t ^ 2)) = 2 * y ^ 2 / t := by
    field_simp [ht0]
  rw [← heq]
  nlinarith

/-- At a saddle of height at least `t*v`, the second derivative
`-2y²B` is at most `-2v²`. This displays the uniform nondegeneracy
coefficient; obtaining `B ≥ t⁻²` from the finite level equation is separate. -/
theorem vertical_curvature_upper (t y B v : ℝ) (ht : 0 < t)
    (hv : 0 ≤ v) (hy : t * v ≤ y) (hJensen : 1 / t ^ 2 ≤ B) :
    -2 * y ^ 2 * B ≤ -2 * v ^ 2 := by
  have hyv : 0 ≤ t * v := mul_nonneg (le_of_lt ht) hv
  have hysq : (t * v) ^ 2 ≤ y ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hyv hy
  have hprod := mul_le_mul hysq hJensen (one_div_nonneg.mpr (sq_nonneg t))
    (sq_nonneg y)
  have heq : (t * v) ^ 2 * (1 / t ^ 2) = v ^ 2 := by
    field_simp [ne_of_gt ht]
  rw [heq] at hprod
  nlinarith

/-- Finite averaged Cauchy–Schwarz for every real vector on a nonempty
finite set. Used with `r j = |z₀-dⱼ|⁻²`; no limit measure is required. -/
theorem square_mean_le_mean_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) :
    ((∑ j, r j) / (Fintype.card ι : ℝ)) ^ 2 ≤
      (∑ j, r j ^ 2) / (Fintype.card ι : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcs : (∑ j, r j) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, r j ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := r))
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hn) hn).mpr
  have hmul := mul_le_mul_of_nonneg_right hcs (le_of_lt hn)
  nlinarith

/-- The finite saddle level equation implies the Jensen bound used
in both curvature estimates. -/
theorem fourth_moment_lower_of_level {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (t : ℝ)
    (hlevel : (∑ j, r j) / (Fintype.card ι : ℝ) = 1 / t) :
    1 / t ^ 2 ≤ (∑ j, r j ^ 2) / (Fintype.card ι : ℝ) := by
  have h := square_mean_le_mean_square r
  rw [hlevel] at h
  simpa only [div_pow, one_pow] using h

end BlockBand.GaussianBulk
