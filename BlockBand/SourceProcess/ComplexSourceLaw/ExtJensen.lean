module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Jensen-type inequalities for the extended source moments

* `weighted_rpow_le`: `(Σ wᵢaᵢ)^p ≤ (Σ wᵢ)^{p-1} Σ wᵢaᵢ^p` for `w, a ≥ 0`, `p ≥ 1`;
* `rpow_lintegral_le`: `(∫⁻ F)^p ≤ ∫⁻ F^p` for a probability measure, `p ≥ 1` (Hölder with
  `g = 1`);
* `rpow_le_one_add`: `x^p ≤ 1 + x^{p'}` for `x ≥ 0`, `0 ≤ p ≤ p'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory
open scoped ENNReal

/-- **Weighted Jensen** for `x ↦ x^p`. -/
theorem weighted_rpow_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * a i) ^ p ≤ (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, w i * a i ^ p := by
  have hS0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hp0 : p ≠ 0 := by linarith
  rcases hS0.eq_or_lt with h0 | hS
  · have hw0 : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).1 h0.symm
    have e1 : ∑ i ∈ s, w i * a i = 0 := Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
    have e2 : ∑ i ∈ s, w i * a i ^ p = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
    rw [e1, e2, Real.zero_rpow hp0, mul_zero]
  · set S := ∑ i ∈ s, w i
    have J := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / S) a
      (fun i hi => div_nonneg (hw i hi) hS.le) (by rw [← Finset.sum_div, div_self hS.ne'])
      ha hp
    have e1 : ∑ i ∈ s, w i / S * a i = (∑ i ∈ s, w i * a i) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ s, w i / S * a i ^ p = (∑ i ∈ s, w i * a i ^ p) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, Real.div_rpow (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (ha i hi))
      hS.le] at J
    have hSp : 0 < S ^ p := Real.rpow_pos_of_pos hS p
    rw [div_le_div_iff₀ hSp hS] at J
    rw [Real.rpow_sub_one hS.ne', div_mul_eq_mul_div, le_div_iff₀ hS]
    linarith

/-- **Jensen in `ℝ≥0∞`**: `(∫⁻ F)^p ≤ ∫⁻ F^p` for a probability measure and `p ≥ 1`. -/
theorem rpow_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F : α → ℝ≥0∞} (hF : AEMeasurable F μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ a, F a ∂μ) ^ p ≤ ∫⁻ a, F a ^ p ∂μ := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.conjExponent hp1) hF
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  calc (∫⁻ a, F a ∂μ) ^ p ≤ ((∫⁻ a, F a ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h (by linarith)
    _ = ∫⁻ a, F a ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel (by linarith), ENNReal.rpow_one]

/-- `x^p ≤ 1 + x^{p'}` for `x ≥ 0`, `0 ≤ p ≤ p'`. -/
theorem rpow_le_one_add {x p p' : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) (hpp' : p ≤ p') :
    x ^ p ≤ 1 + x ^ p' := by
  have h0 : 0 ≤ x ^ p' := Real.rpow_nonneg hx p'
  rcases le_total x 1 with h1 | h1
  · have := Real.rpow_le_one hx h1 hp
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1 hpp'
    linarith

end BlockBand.SourceProcess.ComplexSourceLaw
