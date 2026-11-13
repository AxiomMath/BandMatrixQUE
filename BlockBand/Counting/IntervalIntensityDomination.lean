module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Closed-interval bounds imply full intensity domination

If a measure `μ` on `ℝ` satisfies `μ [a,b] ≤ K (b - a)` for every closed interval, then
`μ ≤ K • volume` as measures (for `K > 0`, or for finite `μ` and `K ≥ 0`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set
open scoped ENNReal NNReal

/-- Closed-interval control gives every half-open interval bound, including reversed endpoints. -/
theorem intensity_Ioc_le_of_Icc_le (μ : Measure ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hI : ∀ a b : ℝ, a ≤ b → μ (Icc a b) ≤ ENNReal.ofReal (K * (b - a)))
    (a b : ℝ) : μ (Ioc a b) ≤ ENNReal.ofReal K * ENNReal.ofReal (b - a) := by
  by_cases hab : a ≤ b
  · calc
      _ ≤ μ (Icc a b) := measure_mono Ioc_subset_Icc_self
      _ ≤ ENNReal.ofReal (K * (b - a)) := hI a b hab
      _ = _ := ENNReal.ofReal_mul hK
  · rw [Ioc_eq_empty (not_lt_of_ge (le_of_lt (lt_of_not_ge hab))), measure_empty]
    exact bot_le

/-- For positive `K`, interval envelopes and outer-measure maximality
prove full domination, even without a finiteness assumption on `μ`. -/
theorem intensity_le_volume_of_Icc_le_pos (μ : Measure ℝ) (K : ℝ) (hK : 0 < K)
    (hI : ∀ a b : ℝ, a ≤ b → μ (Icc a b) ≤ ENNReal.ofReal (K * (b - a))) :
    μ ≤ ENNReal.ofReal K • (volume : Measure ℝ) := by
  let c := ENNReal.ofReal K
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hK).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hbot : (botSet : Set ℝ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    change IsBot x at hx
    have h := hx (x - 1)
    linarith
  have hn : (c⁻¹ • μ).toOuterMeasure ≤ StieltjesFunction.id.outer := by
    unfold StieltjesFunction.outer
    apply OuterMeasure.le_ofFunction.mpr
    intro s
    rw [StieltjesFunction.length_eq]
    refine le_iInf fun a => le_iInf fun b => le_iInf fun hs => ?_
    have hs' : s ⊆ Ioc a b := by simpa only [hbot, sdiff_empty] using hs
    change c⁻¹ * μ s ≤ ENNReal.ofReal (b - a)
    calc
      _ ≤ c⁻¹ * (c * ENNReal.ofReal (b - a)) := by
        gcongr
        exact (measure_mono hs').trans (intensity_Ioc_le_of_Icc_le μ K hK.le hI a b)
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  apply Measure.le_iff'.mpr
  intro s
  have hs := hn s
  have hv : (volume : Measure ℝ) s = StieltjesFunction.id.outer s := by
    rw [Real.volume_val, StieltjesFunction.measure]
    rfl
  change c⁻¹ * μ s ≤ StieltjesFunction.id.outer s at hs
  rw [← hv] at hs
  change μ s ≤ (c • (volume : Measure ℝ)) s
  calc
    _ = c * (c⁻¹ * μ s) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
    _ ≤ c * (volume : Measure ℝ) s := by gcongr
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul]

/-- Full Borel/outer measure domination from exactly the closed-interval bound.
The zero constant is included; finiteness of `μ` is used for the case `K = 0`. -/
theorem intensity_le_volume_of_Icc_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K)
    (hI : ∀ a b : ℝ, a ≤ b → μ (Icc a b) ≤ ENNReal.ofReal (K * (b - a))) :
    μ ≤ ENNReal.ofReal K • (volume : Measure ℝ) := by
  rcases eq_or_lt_of_le hK with hzero | hpos
  · have hz : K = 0 := hzero.symm
    subst K
    have hm : μ = 0 := by
      apply Real.measure_ext_Ioo_rat
      intro a b
      apply le_antisymm _ (bot_le)
      calc
        _ ≤ μ (Ioc (a : ℝ) (b : ℝ)) := measure_mono Ioo_subset_Ioc_self
        _ ≤ 0 := by simpa only [ENNReal.ofReal_zero, zero_mul] using
          intensity_Ioc_le_of_Icc_le μ 0 (le_refl 0) hI a b
        _ = _ := by simp
    simp [hm]
  · exact intensity_le_volume_of_Icc_le_pos μ K hpos hI

end BlockBand.Counting
