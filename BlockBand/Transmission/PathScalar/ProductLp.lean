module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `L^p` norms on a product from bounds on the sections

A bound "conditional on the old path" is a bound at every deterministic old input; Fubini turns
it into an unconditional bound.

`eLpNorm_prod_le_of_section`: if `‖Φ(x,·)‖_{L^p(ν)} ≤ c` for `μ`-a.e. `x`, then
`‖Φ‖_{L^p(μ⊗ν)} ≤ c` (`μ` a probability measure).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory
open scoped ENNReal

theorem eLpNorm_prod_le_of_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν] {Φ : α × β → ℝ}
    (hΦ : Measurable Φ) {p c : ℝ} (hp : 0 < p)
    (h : ∀ᵐ x ∂μ, eLpNorm (fun y => Φ (x, y)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal c) :
    eLpNorm Φ (ENNReal.ofReal p) (μ.prod ν) ≤ ENNReal.ofReal c := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hΦ.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, lintegral_prod _ (hΦ.enorm.pow_const _).aemeasurable]
  have hsec : ∀ᵐ x ∂μ, ∫⁻ y, ‖Φ (x, y)‖ₑ ^ p ∂ν ≤ ENNReal.ofReal c ^ p := h.mono fun x hx => by
    have hm : Measurable fun y => Φ (x, y) := hΦ.comp measurable_prodMk_left
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp.le,
      one_div, ENNReal.rpow_inv_le_iff hp] at hx
    exact hx
  calc (∫⁻ x, ∫⁻ y, ‖Φ (x, y)‖ₑ ^ p ∂ν ∂μ) ^ (1 / p)
      ≤ (∫⁻ _x, ENNReal.ofReal c ^ p ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hsec) (by positivity)
    _ = ENNReal.ofReal c := by
        rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end BlockBand.Transmission.PathScalar
