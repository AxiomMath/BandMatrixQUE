module

public import Mathlib

/-!
# Orthogonality of martingale increments to bounded past factors

For a martingale `M` and a bounded `𝓖_s`-measurable `A`, `E[A (M_t − M_s)] = 0`
(`integral_mul_increment_eq_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {𝓖 : Filtration ℝ≥0 m}

theorem integral_mul_eq_of_martingale {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P) {s t : ℝ≥0}
    (hst : s ≤ t) {A : Ω → ℝ} (hA : StronglyMeasurable[𝓖 s] A) {C : ℝ} (hAb : ∀ ω, |A ω| ≤ C) :
    ∫ ω, A ω * M t ω ∂P = ∫ ω, A ω * M s ω ∂P := by
  have hAm : AEStronglyMeasurable A P := (hA.mono (𝓖.le s)).aestronglyMeasurable
  have hAb' : ∀ᵐ ω ∂P, ‖A ω‖ ≤ C := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hAb ω
  have hit : Integrable (A * M t) P := (hM.integrable t).bdd_mul hAm hAb'
  change ∫ ω, (A * M t) ω ∂P = ∫ ω, (A * M s) ω ∂P
  rw [← integral_condExp (𝓖.le s) (f := A * M t)]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hA hit (hM.integrable t),
    hM.condExp_ae_eq hst] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]; rfl

/-- **`E[A (M_t − M_s)] = 0`** for bounded `𝓖_s`-measurable `A`. -/
theorem integral_mul_increment_eq_zero {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P) {s t : ℝ≥0}
    (hst : s ≤ t) {A : Ω → ℝ} (hA : StronglyMeasurable[𝓖 s] A) {C : ℝ} (hAb : ∀ ω, |A ω| ≤ C) :
    ∫ ω, A ω * (M t ω - M s ω) ∂P = 0 := by
  have hAm : AEStronglyMeasurable A P := (hA.mono (𝓖.le s)).aestronglyMeasurable
  have hAb' : ∀ᵐ ω ∂P, ‖A ω‖ ≤ C := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hAb ω
  simp_rw [mul_sub]
  rw [integral_sub ((hM.integrable t).bdd_mul hAm hAb') ((hM.integrable s).bdd_mul hAm hAb'),
    integral_mul_eq_of_martingale hM hst hA hAb, sub_self]

end BlockBand.Transmission.LawDuality
