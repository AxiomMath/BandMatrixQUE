module

public import BlockBand.Coarea.Native.BlockBand.Counting.Factorial

/-!
# Scale-uniform ordinary moment bounds

This file gives the large-window combinatorial step following the PSSS
factorial-count input.  For scale `v ≥ 1`, every monomial
of the Stirling moment polynomial has degree at most the moment order, so the
whole polynomial is bounded by its unit-scale value times `v ^ r`.  Applying
this deterministic estimate to `psss_scaled_countMoment` gives the polynomial
growth in the window radius used in the projected-Wegner counting chain.

The constant is explicit and depends only on the moment order `r` and the
absolute PSSS constant `input.C`; it is uniform in the number and sizes of the
blocks, the deterministic deformation, the energy, and the ambient dimension.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators

universe u

/-- Large-scale Stirling polynomial estimate.  For `v ≥ 1` and positive
moment order `r`, nonnegativity of the Stirling coefficients and the support
condition `j ≤ r` give
`∑ j, S(r,j) (C v)^j ≤ v^r ∑ j, S(r,j) C^j`.
The constant is independent of `v`. -/
theorem stirlingMomentPolynomial_large
    (r : ℕ) (_hr : 1 ≤ r) {C v : ℝ}
    (hC : 0 ≤ C) (hv : 1 ≤ v) :
    ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (C * v) ^ j ≤
      v ^ r * ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * C ^ j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    (r.stirlingSecond j : ℝ) * (C * v) ^ j =
        ((r.stirlingSecond j : ℝ) * C ^ j) * v ^ j := by
          rw [mul_pow]
          ring
    _ ≤ ((r.stirlingSecond j : ℝ) * C ^ j) * v ^ r := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_right₀ hv hjr
          · positivity
    _ = v ^ r * ((r.stirlingSecond j : ℝ) * C ^ j) := by ring

/-- Large-window specialization of `psss_scaled_countMoment`.  At every scale
`v ≥ 1`, the `r`th moment of the eigenvalue count in the interval
`[e-v/L,e+v/L]` is at most an explicit constant times `v^r`.  The deterministic deformation is arbitrary,
`L` only dominates the total block dimension, and the constant is uniform in
all of those choices. -/
theorem psss_scaled_countMoment_large
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e v L : ℝ) (hv : 1 ≤ v) (hL : 0 < L)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω,
        (BlockGUE.intervalCount M A₀
          (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P ≤
      (∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j) * v ^ r := by
  calc
    ∫ ω,
        (BlockGUE.intervalCount M A₀
          (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P ≤
      ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C * v) ^ j :=
      psss_scaled_countMoment input hd M A₀ e v L (le_trans (by norm_num) hv)
        hL hdim r
    _ ≤ v ^ r * ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j := by
      exact stirlingMomentPolynomial_large r hr
        (mul_nonneg (by norm_num) input.C_nonneg) hv
    _ = (∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j) * v ^ r := by
      ring

end CoareaNative.BlockBand
