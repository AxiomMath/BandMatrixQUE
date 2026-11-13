module

public import Mathlib

/-!
# `L^p` tools for the refined count

Fubini and moment inequalities used to pass from conditional to unconditional bounds.

* `eLpNorm_prod_le_of_slices` — a uniform bound on the fresh slices `‖f(a,·)‖_{L^q(γ)} ≤ B`
  gives `‖f‖_{L^q(ν ⊗ γ)} ≤ B` (the conditional-to-unconditional step, Fubini).
* `eLpNorm_sub_integral_le` — `‖g - Eg‖_q ≤ 2‖g‖_q`.
* `eLpNorm_le_of_sq_bound` — `|M| ≤ A D² + B`, `‖D‖_{2q} ≤ δ` give `‖M‖_q ≤ A δ² + B`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory
open scoped ENNReal

theorem eLpNorm_prod_le_of_slices {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (γ : Measure β) [IsProbabilityMeasure ν] [SFinite γ]
    (f : α × β → ℝ) (hf : AEStronglyMeasurable f (ν.prod γ)) {q B : ℝ} (hq : 1 ≤ q)
    (h : ∀ a, eLpNorm (fun y => f (a, y)) (ENNReal.ofReal q) γ ≤ ENNReal.ofReal B) :
    eLpNorm f (ENNReal.ofReal q) (ν.prod γ) ≤ ENNReal.ofReal B := by
  have hq0 : (ENNReal.ofReal q) ≠ 0 := by simp; linarith
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal (by linarith)
  have hqpos : 0 < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hf, hqr]
  have hslice : ∀ a, (∫⁻ y, ‖f (a, y)‖ₑ ^ q ∂γ) ≤ ENNReal.ofReal B ^ q := by
    intro a
    have h1 := h a
    by_cases hm : AEStronglyMeasurable (fun y => f (a, y)) γ
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hm, hqr] at h1
      have h2 := ENNReal.rpow_le_rpow h1 hqpos.le
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hqpos.ne', ENNReal.rpow_one] at h2
    · rw [eLpNorm_of_not_aestronglyMeasurable hm] at h1
      exact absurd h1 (by simp)
  calc (∫⁻ z, ‖f z‖ₑ ^ q ∂ν.prod γ) ^ (1 / q)
      ≤ (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ q ∂γ ∂ν) ^ (1 / q) := by
        gcongr; exact lintegral_prod_le _
    _ ≤ (∫⁻ _ : α, ENNReal.ofReal B ^ q ∂ν) ^ (1 / q) := by
        gcongr with x; exact hslice x
    _ = ENNReal.ofReal B := by
        rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
          mul_one_div_cancel hqpos.ne', ENNReal.rpow_one]

theorem eLpNorm_sub_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun ω => g ω - ∫ ω', g ω' ∂μ) (ENNReal.ofReal q) μ ≤
      2 * eLpNorm g (ENNReal.ofReal q) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  by_cases hm : AEStronglyMeasurable g μ
  · have hc : eLpNorm (fun _ : Ω => ∫ ω', g ω' ∂μ) (ENNReal.ofReal q) μ ≤
        eLpNorm g (ENNReal.ofReal q) μ := by
      rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
        ENNReal.one_rpow, mul_one]
      calc ‖∫ ω', g ω' ∂μ‖ₑ ≤ ∫⁻ ω, ‖g ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
        _ = eLpNorm g 1 μ := (eLpNorm_one_eq_lintegral_enorm hm).symm
        _ ≤ eLpNorm g (ENNReal.ofReal q) μ := eLpNorm_le_eLpNorm_of_exponent_le hp1
    calc _ ≤ eLpNorm g (ENNReal.ofReal q) μ +
          eLpNorm (fun _ : Ω => ∫ ω', g ω' ∂μ) (ENNReal.ofReal q) μ :=
          eLpNorm_sub_le (f := g) (g := fun _ => ∫ ω', g ω' ∂μ) hp1
      _ ≤ eLpNorm g (ENNReal.ofReal q) μ + eLpNorm g (ENNReal.ofReal q) μ := by gcongr
      _ = 2 * eLpNorm g (ENNReal.ofReal q) μ := by rw [two_mul]
  · rw [eLpNorm_of_not_aestronglyMeasurable hm]; simp

theorem eLpNorm_le_of_sq_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M D : Ω → ℝ) (hD : AEStronglyMeasurable D μ)
    (hM : AEStronglyMeasurable M μ) (hD0 : ∀ ω, 0 ≤ D ω) {q A B δ : ℝ} (hq : 1 ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hpt : ∀ᵐ ω ∂μ, |M ω| ≤ A * D ω ^ 2 + B)
    (hDq : eLpNorm D (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal δ) :
    eLpNorm M (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (A * δ ^ 2 + B) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hsq : eLpNorm (fun ω => D ω ^ 2) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (δ ^ 2) := by
    have heq : (fun ω => D ω ^ 2) = fun ω => ‖D ω‖ ^ (2 : ℝ) := by
      funext ω; rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ω), Real.rpow_two]
    rw [heq, eLpNorm_norm_rpow D hD (by norm_num), ← ENNReal.ofReal_mul (by linarith),
      mul_comm q 2]
    calc eLpNorm D (ENNReal.ofReal (2 * q)) μ ^ (2 : ℝ) ≤ ENNReal.ofReal δ ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hDq (by norm_num)
      _ = ENNReal.ofReal (δ ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num), Real.rpow_two]
  calc eLpNorm M (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun ω => A * D ω ^ 2 + B) (ENNReal.ofReal q) μ := by
        refine eLpNorm_mono_ae_real hM (hpt.mono fun ω h => ?_)
        rwa [Real.norm_eq_abs]
    _ ≤ eLpNorm (fun ω => A * D ω ^ 2) (ENNReal.ofReal q) μ +
        eLpNorm (fun _ : Ω => B) (ENNReal.ofReal q) μ :=
        eLpNorm_add_le (f := fun ω => A * D ω ^ 2) (g := fun _ => B) hp1
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (δ ^ 2) + ENNReal.ofReal B := by
        gcongr
        · have : (fun ω => A * D ω ^ 2) = A • fun ω => D ω ^ 2 := rfl
          rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hA]
          gcongr
        · rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
            ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hB]
    _ = ENNReal.ofReal (A * δ ^ 2 + B) := by
        rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) hB]

end BlockBand.Window.Count
