module

public import BlockBand.Transmission.LawDecay.Gen
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Bounds and measurability of `Φ_ε` and its coefficients

On `0 ≤ y ≤ x`, with `U = ε^{-1/2}`, every coefficient `coefX, coefY, coefXX, coefXY` is
bounded by `U⁵` (`coef_bounds`), and `|Φ_ε(x,y)| ≤ x + 2` if moreover `y ≤ x²`
(`abs_lyap_le`). All four coefficients and `Φ_ε` are Borel functions of `(x, y)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

/-- **Coefficient bounds** on `0 ≤ y ≤ x`. -/
theorem coef_bounds {ε x y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x) :
    |coefX ε x y| ≤ (Real.sqrt ε)⁻¹ ^ 5 ∧ |coefY ε x| ≤ (Real.sqrt ε)⁻¹ ^ 5 ∧
      |coefXX ε x y| ≤ (Real.sqrt ε)⁻¹ ^ 5 ∧ |coefXY ε x| ≤ (Real.sqrt ε)⁻¹ ^ 5 := by
  have hs : 0 < x + ε := by linarith
  set U := (Real.sqrt ε)⁻¹
  set a := Real.sqrt (x + ε)
  have ha : 0 < a := Real.sqrt_pos.2 hs
  have ha2 : a ^ 2 = x + ε := Real.sq_sqrt hs.le
  have he : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hea : Real.sqrt ε ≤ a := Real.sqrt_le_sqrt (by linarith)
  have he1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  set u := a⁻¹
  have hu0 : 0 < u := inv_pos.2 ha
  have huU : u ≤ U := inv_anti₀ he hea
  have hU1 : 1 ≤ U := one_le_inv₀ he |>.2 he1
  have hyu : y * u ^ 2 ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity), ha2]; linarith
  have hu1 : u ≤ U ^ 5 := huU.trans (le_self_pow₀ hU1 (by norm_num))
  have hu3 : u ^ 3 ≤ U ^ 5 :=
    (pow_le_pow_left₀ hu0.le huU 3).trans (pow_le_pow_right₀ hU1 (by norm_num))
  have hu5 : u ^ 5 ≤ U ^ 5 := pow_le_pow_left₀ hu0.le huU 5
  have e1 := rpow_n1 hs
  have e3 := rpow_n3 hs
  have e5 := rpow_n5 hs
  have e7 := rpow_n7 hs
  rw [← inv_pow] at e1 e3 e5 e7
  have hy5 : y * u ^ 5 ≤ u ^ 3 := by
    have : y * u ^ 5 = y * u ^ 2 * u ^ 3 := by ring
    rw [this]; exact mul_le_of_le_one_left (by positivity) hyu
  have hy7 : y * u ^ 7 ≤ u ^ 5 := by
    have : y * u ^ 7 = y * u ^ 2 * u ^ 5 := by ring
    rw [this]; exact mul_le_of_le_one_left (by positivity) hyu
  have hyu5 : 0 ≤ y * u ^ 5 := by positivity
  have hyu7 : 0 ≤ y * u ^ 7 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coefX, e1, e5, abs_of_nonneg (by positivity)]
    simp only [pow_one] at *
    nlinarith
  · rw [coefY, e3, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  · rw [coefXX, e3, e7]
    rw [abs_le]; constructor <;> nlinarith
  · rw [coefXY, e5, abs_of_nonneg (by positivity)]
    nlinarith

/-- `|Φ_ε(x, y)| ≤ x + 2` for `0 ≤ y ≤ x²`, `0 < ε ≤ 1`. -/
theorem abs_lyap_le {ε x y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hyx : y ≤ x ^ 2) : |lyap ε x y| ≤ x + 2 := by
  obtain ⟨h1, h2⟩ := lyap_bounds hε hx hy hyx
  have hs := Real.sqrt_nonneg (x + ε)
  have hsq : Real.sqrt (x + ε) ^ 2 = x + ε := Real.sq_sqrt (by linarith)
  rw [abs_of_nonneg (by linarith)]
  nlinarith

theorem measurable_lyap (ε : ℝ) : Measurable fun p : ℝ × ℝ => lyap ε p.1 p.2 := by
  unfold lyap; fun_prop

theorem measurable_coefX (ε : ℝ) : Measurable fun p : ℝ × ℝ => coefX ε p.1 p.2 := by
  unfold coefX; fun_prop

theorem measurable_coefY (ε : ℝ) : Measurable fun x : ℝ => coefY ε x := by
  unfold coefY; fun_prop

theorem measurable_coefXX (ε : ℝ) : Measurable fun p : ℝ × ℝ => coefXX ε p.1 p.2 := by
  unfold coefXX; fun_prop

theorem measurable_coefXY (ε : ℝ) : Measurable fun x : ℝ => coefXY ε x := by
  unfold coefXY; fun_prop

end BlockBand.Transmission.LawDecay
