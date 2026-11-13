module

public import Mathlib
public import BlockBand.External.Johansson.SourceStatement

/-!
# Gaussian domination of the Johansson vertical integrand

Used for the continuity of Johansson's double contour integral kernel. For the
integrand `Johansson.kernelIntegrand S d u v z w` on the upward line `w = L + iy` (`S > 0`
real time, arbitrary real source `d : Fin N → ℝ`, possibly repeated), we prove the explicit
bound

`‖kernelIntegrand S d u v z (L+iy)‖ ≤ kernelBoundConst S N L B δ c · exp(-y²/(4S))`

whenever `‖z‖, |u|, |v|, |d_j| ≤ B`, `L - Re z ≥ δ > 0` and `‖z - d_j‖ ≥ c_j > 0`. Hence the
vertical integrand is Lebesgue integrable (`integrable_kernelIntegrand_line`) for every real
source `d`; `Johansson.SourceContract` asserts this only for strictly increasing `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory
open BlockBand.External
open scoped NNReal

/-- The explicit constant in the Gaussian domination of the vertical integrand. -/
def kernelBoundConst (S : ℝ≥0) (N : ℕ) (L B δ : ℝ) (c : Fin N → ℝ) : ℝ :=
  Real.exp ((L ^ 2 + 2 * B * |L| + 3 * B ^ 2) / (2 * S)) * δ⁻¹ * (∏ j, (c j)⁻¹) *
    (N.factorial : ℝ) * Real.exp ((|L| + B + 1) + (|L| + B + 1) ^ 2 * S)

/-- The domination constant is nonnegative. -/
theorem kernelBoundConst_nonneg (S : ℝ≥0) (N : ℕ) (L B δ : ℝ) (c : Fin N → ℝ)
    (hc : ∀ j, 0 < c j) (hδ : 0 < δ) : 0 ≤ kernelBoundConst S N L B δ c := by
  unfold kernelBoundConst
  have : 0 ≤ ∏ j, (c j)⁻¹ := Finset.prod_nonneg (fun j _ => (inv_pos.mpr (hc j)).le)
  positivity

/-- Gaussian domination of the Johansson integrand on the line `Re w = L`. -/
theorem norm_kernelIntegrand_le {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (u v L y : ℝ) (z : ℂ) (B δ : ℝ) (c : Fin N → ℝ) (hc : ∀ j, 0 < c j)
    (hzd : ∀ j, c j ≤ ‖z - (d j : ℂ)‖) (hδ : 0 < δ) (hLz : δ ≤ L - z.re)
    (hzB : ‖z‖ ≤ B) (huB : |u| ≤ B) (hvB : |v| ≤ B) (hdB : ∀ j, |d j| ≤ B) :
    ‖Johansson.kernelIntegrand S d u v z ((L : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      kernelBoundConst S N L B δ c * Real.exp (-(1 / (4 * S)) * y ^ 2) := by
  set w : ℂ := (L : ℂ) + (y : ℂ) * Complex.I with hw
  have hSr : (0 : ℝ) < S := hS
  have hB0 : 0 ≤ B := (norm_nonneg z).trans hzB
  set A : ℝ := |L| + B + 1 with hA
  have hA1 : 1 ≤ A := by have := abs_nonneg L; linarith
  -- exponential factor
  have hexp : ‖Complex.exp ((w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z) /
      (2 * ((S : ℝ) : ℂ)))‖ ≤
      Real.exp ((L ^ 2 + 2 * B * |L| + 3 * B ^ 2) / (2 * S) - y ^ 2 / (2 * S)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [show (2 * ((S : ℝ) : ℂ)) = ((2 * (S : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re]
    have hnum : (w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z).re =
        L ^ 2 - y ^ 2 - 2 * v * L - (z.re ^ 2 - z.im ^ 2) + 2 * u * z.re := by
      simp [hw, sq, Complex.mul_re, Complex.mul_im]
    rw [hnum, ← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : |v * L| ≤ B * |L| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hvB (abs_nonneg _)
    have h2 : z.im ^ 2 ≤ B ^ 2 := by
      have := (Complex.abs_im_le_norm z).trans hzB
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h3 : |u * z.re| ≤ B * B := by
      rw [abs_mul]
      exact mul_le_mul huB ((Complex.abs_re_le_norm z).trans hzB) (abs_nonneg _) hB0
    have h4 := neg_abs_le (v * L)
    have h5 := le_abs_self (u * z.re)
    nlinarith [sq_nonneg z.re]
  -- denominator `w - z`
  have hwz : δ ≤ ‖w - z‖ := by
    have hre : (w - z).re = L - z.re := by simp [hw]
    calc δ ≤ L - z.re := hLz
      _ = (w - z).re := hre.symm
      _ ≤ |(w - z).re| := le_abs_self _
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  have hwz0 : 0 < ‖w - z‖ := lt_of_lt_of_le hδ hwz
  -- product factor
  have hwnorm : ‖w‖ ≤ |L| + |y| := by
    calc ‖w‖ ≤ ‖(L : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |L| + |y| := by simp [Complex.norm_real]
  have hprod : ‖∏ j, (w - (d j : ℂ)) / (z - (d j : ℂ))‖ ≤
      (A * (1 + |y|)) ^ N * ∏ j, (c j)⁻¹ := by
    rw [norm_prod]
    calc ∏ j, ‖(w - (d j : ℂ)) / (z - (d j : ℂ))‖ ≤ ∏ _j : Fin N, (A * (1 + |y|) * (c _j)⁻¹) := by
          apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
          intro j _
          rw [norm_div]
          have hnum : ‖w - (d j : ℂ)‖ ≤ A * (1 + |y|) := by
            calc ‖w - (d j : ℂ)‖ ≤ ‖w‖ + ‖(d j : ℂ)‖ := norm_sub_le _ _
              _ ≤ |L| + |y| + B := by
                rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hdB j]
              _ ≤ A * (1 + |y|) := by
                have := abs_nonneg y
                nlinarith [abs_nonneg L]
          rw [div_eq_mul_inv]
          exact mul_le_mul hnum (inv_anti₀ (hc j) (hzd j)) (inv_nonneg.mpr (norm_nonneg _))
            (by positivity)
      _ = (A * (1 + |y|)) ^ N * ∏ j, (c j)⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- polynomial factor against half of the Gaussian
  have hpoly : (A * (1 + |y|)) ^ N ≤
      (N.factorial : ℝ) * Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S)) := by
    have hX : 0 ≤ A * (1 + |y|) := by positivity
    have h1 := Real.pow_div_factorial_le_exp (A * (1 + |y|)) hX N
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hfac] at h1
    refine h1.trans ?_
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hfac.le
    apply Real.exp_le_exp.mpr
    have hy := abs_nonneg y
    have key : A * |y| ≤ A ^ 2 * S + y ^ 2 / (4 * S) := by
      rw [← sq_abs y]
      have h4S : (0 : ℝ) < 4 * S := by positivity
      have hid : A ^ 2 * S + |y| ^ 2 / (4 * S) - A * |y| = (2 * A * S - |y|) ^ 2 / (4 * S) := by
        field_simp
        ring
      have : 0 ≤ (2 * A * S - |y|) ^ 2 / (4 * S) := by positivity
      linarith
    nlinarith
  -- assemble
  unfold Johansson.kernelIntegrand
  rw [norm_mul, norm_div]
  have hC0 : 0 ≤ ∏ j, (c j)⁻¹ := Finset.prod_nonneg (fun j _ => (inv_pos.mpr (hc j)).le)
  have hS2 : ((S : ℂ)) = (((S : ℝ)) : ℂ) := rfl
  rw [hS2]
  calc ‖Complex.exp ((w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z) /
          (2 * ((S : ℝ) : ℂ)))‖ / ‖w - z‖ * ‖∏ j, (w - (d j : ℂ)) / (z - (d j : ℂ))‖
      ≤ Real.exp ((L ^ 2 + 2 * B * |L| + 3 * B ^ 2) / (2 * S) - y ^ 2 / (2 * S)) / δ *
          ((N.factorial : ℝ) * Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S)) * ∏ j, (c j)⁻¹) := by
        apply mul_le_mul _ (hprod.trans (mul_le_mul_of_nonneg_right hpoly hC0))
          (norm_nonneg _) (by positivity)
        exact div_le_div₀ (by positivity) hexp hδ hwz
    _ = kernelBoundConst S N L B δ c * Real.exp (-(1 / (4 * S)) * y ^ 2) := by
        unfold kernelBoundConst
        rw [← hA]
        have e1 : Real.exp ((L ^ 2 + 2 * B * |L| + 3 * B ^ 2) / (2 * S) - y ^ 2 / (2 * S)) =
            Real.exp ((L ^ 2 + 2 * B * |L| + 3 * B ^ 2) / (2 * S)) *
              Real.exp (-(y ^ 2 / (2 * S))) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (A + A ^ 2 * S + y ^ 2 / (4 * S)) =
            Real.exp (A + A ^ 2 * S) * Real.exp (y ^ 2 / (4 * S)) := by
          rw [← Real.exp_add]
        have e3 : Real.exp (-(y ^ 2 / (2 * S))) * Real.exp (y ^ 2 / (4 * S)) =
            Real.exp (-(1 / (4 * S)) * y ^ 2) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        rw [e1, e2, div_eq_mul_inv, ← e3]
        ring

/-- The vertical (2.18) integrand is Lebesgue integrable in `y` for every real source `d`
(possibly repeated) and every `z` with `Re z < L` and `z ≠ d_j` for all `j`. -/
theorem integrable_kernelIntegrand_line {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (u v L : ℝ) (z : ℂ) (hzL : z.re < L) (hzd : ∀ j, z ≠ (d j : ℂ)) :
    Integrable (fun y : ℝ => Complex.I *
      Johansson.kernelIntegrand S d u v z ((L : ℂ) + (y : ℂ) * Complex.I)) := by
  have hSr : (0 : ℝ) < S := hS
  set B : ℝ := ‖z‖ + |u| + |v| + ∑ j, |d j| with hB
  have hsum : ∀ j, |d j| ≤ ∑ j, |d j| :=
    fun j => Finset.single_le_sum (f := fun j => |d j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hc : ∀ j, 0 < ‖z - (d j : ℂ)‖ := fun j => norm_pos_iff.mpr (sub_ne_zero.mpr (hzd j))
  have hg : Integrable (fun y : ℝ =>
      kernelBoundConst S N L B (L - z.re) (fun j => ‖z - (d j : ℂ)‖) *
        Real.exp (-(1 / (4 * S)) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (4 * S))).const_mul _
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · apply Measurable.aestronglyMeasurable
    unfold Johansson.kernelIntegrand
    fun_prop
  · rw [norm_mul, Complex.norm_I, one_mul]
    apply norm_kernelIntegrand_le S hS d u v L y z B (L - z.re) _ hc (fun j => le_rfl)
      (by linarith) le_rfl
    · rw [hB]; have := abs_nonneg u; have := abs_nonneg v
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (d j)); linarith
    · rw [hB]; have := norm_nonneg z; have := abs_nonneg v
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (d j)); linarith
    · rw [hB]; have := norm_nonneg z; have := abs_nonneg u
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (d j)); linarith
    · intro j; rw [hB]; have := norm_nonneg z; have := abs_nonneg u; have := abs_nonneg v
      linarith [hsum j]

end BlockBand.GaussianBulk
