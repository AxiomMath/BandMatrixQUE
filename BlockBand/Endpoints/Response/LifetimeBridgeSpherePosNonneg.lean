module

public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePosIntegral
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Nonnegativity of the spherical kernel

This file proves `lbkp_series_nonneg`: for `D₀ > 0`, `t > 0` and `y, y' ∈ [0,1]`,
`0 ≤ lbkSphereSeries D0 t y y'`.

Proof. Put `f = k_t(y, ·)` (continuous on `[0,1]`) and suppose `f y' < 0`. Let
`g = max(-f, 0) ∈ C([0,1])`. Its Bernstein approximations `Bₙ g = Σₖ g(k/n) C(n,k) Xᵏ(1-X)ⁿ⁻ᵏ`
lie in the Bernstein cone `LbkpCone n`, so `∫₀¹ f Bₙ g ≥ 0`
(`lbkp_integral_series_cone_nonneg`); since `Bₙ g → g` uniformly (Mathlib's
`bernsteinApproximation_uniform`), `∫₀¹ f g ≥ 0`. But `f g = -g²` and `g(y') > 0`, so
`∫₀¹ f g < 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Polynomial
open scoped Interval unitInterval

/-- The Bernstein polynomial `Σₖ g(k/n) C(n,k) Xᵏ(1-X)ⁿ⁻ᵏ` of `g ∈ C([0,1])`. -/
def lbkpBernApprox (g : C(I, ℝ)) (n : ℕ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (g (bernstein.z k) * (n.choose k : ℝ)) * lbkpBern n k

theorem lbkp_bernApprox_cone {g : C(I, ℝ)} (hg : ∀ x, 0 ≤ g x) (n : ℕ) :
    LbkpCone n (lbkpBernApprox g n) :=
  lbkp_cone_sum _ _ fun k _ =>
    lbkp_cone_smul (mul_nonneg (hg _) (by positivity)) (lbkp_cone_gen (Nat.lt_succ_iff.1 k.2))

theorem lbkp_bernApprox_eval (g : C(I, ℝ)) (n : ℕ) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    (lbkpBernApprox g n).eval w = bernsteinApproximation n g ⟨w, hw⟩ := by
  rw [bernsteinApproximation.apply, lbkpBernApprox, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bernstein_apply, smul_eq_mul]
  simp only [lbkpBern, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  ring

/-- Nonnegativity of the spherical kernel on `[0,1]²` for `t > 0`. -/
theorem lbkp_series_nonneg {D0 t y y' : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) : 0 ≤ lbkSphereSeries D0 t y y' := by
  set f := lbkSphereSeries D0 t y with hfdef
  have hf : ContinuousOn f (Icc 0 1) := lbk_sphereSeries_continuousOn hD0 ht hy
  by_contra hneg
  rw [not_le] at hneg
  have hfI : Continuous fun x : I => f x :=
    hf.comp_continuous continuous_subtype_val fun x => x.2
  let g : C(I, ℝ) := ⟨fun x => max (-f x) 0, hfI.neg.max continuous_const⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  let G : ℝ → ℝ := fun w => g (projIcc 0 1 zero_le_one w)
  have hGc : Continuous G := g.continuous.comp continuous_projIcc
  have hGeq : ∀ w (hw : w ∈ Icc (0 : ℝ) 1), G w = max (-f w) 0 := by
    intro w hw
    simp only [G, projIcc_of_mem zero_le_one hw]
    rfl
  -- the bound `|f| ≤ M` on `[0,1]`
  set M := ∑' n, lbkYBound D0 t n with hMdef
  have hM : ∀ w ∈ Icc (0 : ℝ) 1, ‖f w‖ ≤ M := fun w hw => lbkp_series_norm_le hD0 ht hy hw
  -- `∫ f Bₙ g → ∫ f G`
  have hconv : Tendsto (fun n => ∫ w in (0 : ℝ)..1, f w * (lbkpBernApprox g n).eval w) atTop
      (𝓝 (∫ w in (0 : ℝ)..1, f w * G w)) := by
    have hu := tendsto_iff_norm_sub_tendsto_zero.1 (bernsteinApproximation_uniform g)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa using (hu.const_mul M).mul_const (1 : ℝ))
    rw [← intervalIntegral.integral_sub]
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M * ‖bernsteinApproximation n g - g‖) fun w hw => ?_).trans ?_
      · have hw' := lbkp_uIoc_sub hw
        rw [← mul_sub, norm_mul]
        refine mul_le_mul (hM w hw') ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM w hw'))
        rw [lbkp_bernApprox_eval g n hw']
        have : G w = g ⟨w, hw'⟩ := by simp only [G, projIcc_of_mem zero_le_one hw']
        rw [this]
        exact ContinuousMap.norm_coe_le_norm (bernsteinApproximation n g - g) ⟨w, hw'⟩
      · simp
    · exact lbkp_series_intervalIntegrable_mul hD0 ht hy (lbkpBernApprox g n).continuous.continuousOn
    · exact lbkp_series_intervalIntegrable_mul hD0 ht hy hGc.continuousOn
  have hlim : 0 ≤ ∫ w in (0 : ℝ)..1, f w * G w :=
    ge_of_tendsto' hconv fun n =>
      lbkp_integral_series_cone_nonneg hD0 ht hy (lbkp_bernApprox_cone hg0 n)
  -- but `f G = -G²` and `G y' > 0`
  have hneg' : (∫ w in (0 : ℝ)..1, f w * G w) = -∫ w in (0 : ℝ)..1, G w * G w := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le zero_le_one] at hw
    simp only [hGeq w hw]
    rcases le_total 0 (f w) with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]; ring
  have hpos : 0 < ∫ w in (0 : ℝ)..1, G w * G w := by
    refine lbkp_integral_pos (hGc.mul hGc).continuousOn (fun w _ => mul_self_nonneg _) hy' ?_
    rw [hGeq y' hy', max_eq_left (by linarith)]
    nlinarith
  linarith

end BlockBand.Endpoints
