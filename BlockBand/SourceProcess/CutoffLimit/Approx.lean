module

public import BlockBand.SourceProcess.SourcePins.AtomFinite

/-!
# Continuous approximants of `ψ_{1/2}`

The continuous functions `g_n = min((n+1)² y, 1/max(√y, 1/(n+1)))` on `[0,1]` are nonnegative,
lie below `ψ_{1/2}` and converge to it pointwise, so by Fatou `∫ ψ_{1/2} dν ≤ liminf_n ∫ g_n dν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory Filter Topology
open BlockBand.SourceProcess.SourcePins
open scoped ENNReal NNReal

/-- The approximant `g_n`. -/
def gApprox (n : ℕ) (y : unitInterval) : ℝ :=
  min (((n : ℝ) + 1) ^ 2 * y) (1 / max (Real.sqrt y) (1 / ((n : ℝ) + 1)))

theorem max_sqrt_pos (n : ℕ) (y : unitInterval) :
    0 < max (Real.sqrt y) (1 / ((n : ℝ) + 1)) :=
  lt_max_of_lt_right (by positivity)

theorem continuous_gApprox (n : ℕ) : Continuous (gApprox n) := by
  unfold gApprox
  refine Continuous.min (continuous_const.mul continuous_subtype_val) ?_
  exact continuous_const.div (Continuous.max (Real.continuous_sqrt.comp continuous_subtype_val)
    continuous_const) fun y => (max_sqrt_pos n y).ne'

theorem gApprox_nonneg (n : ℕ) (y : unitInterval) : 0 ≤ gApprox n y :=
  le_min (mul_nonneg (by positivity) y.2.1) (le_of_lt (by have := max_sqrt_pos n y; positivity))

theorem gApprox_le_psiP (n : ℕ) (y : unitInterval) :
    ENNReal.ofReal (gApprox n y) ≤ psiP (1 / 2) y := by
  rcases y.2.1.eq_or_lt with hy | hy
  · have : gApprox n y = 0 := by
      unfold gApprox
      rw [← hy, mul_zero]
      exact min_eq_left (le_of_lt (by have := max_sqrt_pos n y; positivity))
    rw [this, ENNReal.ofReal_zero]
    exact zero_le
  · rw [psiP, ite_eq_left hy]
    refine ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ?_)
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow,
      ← one_div]
    exact one_div_le_one_div_of_le hs (le_max_left _ _)

theorem gApprox_eventually (y : unitInterval) (hy : 0 < (y : ℝ)) :
    ∀ᶠ n : ℕ in atTop, gApprox n y = 1 / Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / Real.sqrt y) (1 / (y * Real.sqrt y)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : max (1 / Real.sqrt y) (1 / (y * Real.sqrt y)) ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hA : 1 / Real.sqrt y ≤ (n : ℝ) + 1 := (le_max_left _ _).trans hn1
  have hB : 1 / (y * Real.sqrt y) ≤ (n : ℝ) + 1 := (le_max_right _ _).trans hn1
  have hmax : max (Real.sqrt y) (1 / ((n : ℝ) + 1)) = Real.sqrt y := by
    refine max_eq_left ?_
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hs] at hA
    linarith
  unfold gApprox
  rw [hmax]
  refine min_eq_right ?_
  have hys : 0 < y * Real.sqrt y := mul_pos hy hs
  rw [div_le_iff₀ hys] at hB
  have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [div_le_iff₀ hs]
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) * (y * Real.sqrt y) := by linarith
  nlinarith

theorem tendsto_gApprox (y : unitInterval) :
    Tendsto (fun n => ENNReal.ofReal (gApprox n y)) atTop (𝓝 (psiP (1 / 2) y)) := by
  rcases y.2.1.eq_or_lt with hy | hy
  · have h0 : ∀ n, gApprox n y = 0 := fun n => by
      unfold gApprox
      rw [← hy, mul_zero]
      exact min_eq_left (le_of_lt (by have := max_sqrt_pos n y; positivity))
    have hp : psiP (1 / 2) y = 0 := by rw [psiP, ite_eq_right (by rw [← hy]; exact lt_irrefl 0)]
    simp only [h0, ENNReal.ofReal_zero, hp]
    exact tendsto_const_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [gApprox_eventually y hy] with n hn
    rw [hn, psiP, ite_eq_left hy, show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hy.le,
      ← Real.sqrt_eq_rpow, ← one_div]

/-- Fatou: `∫ ψ_{1/2} dν ≤ liminf_n ∫ g_n dν`. -/
theorem lintegral_psiP_le_liminf (ν : Measure unitInterval) :
    ∫⁻ y, psiP (1 / 2) y ∂ν ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (gApprox n y) ∂ν) atTop := by
  calc ∫⁻ y, psiP (1 / 2) y ∂ν
      = ∫⁻ y, liminf (fun n => ENNReal.ofReal (gApprox n y)) atTop ∂ν :=
        lintegral_congr fun y => (tendsto_gApprox y).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le fun n => (continuous_gApprox n).measurable.ennreal_ofReal

end BlockBand.SourceProcess.CutoffLimit
