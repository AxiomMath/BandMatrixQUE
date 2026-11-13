module
public import Mathlib.Probability.ConditionalProbability
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram uniqueness: laws glued from conditional laws on finitely many strata

* `map_eq_of_cond_strata`: on two finite measure spaces with measurable stratum indices
  `k₁, k₂` into a finite type: if the strata have equal masses and, on each stratum of positive
  mass, the conditional laws of `Φ₁, Φ₂` agree, then the laws of `Φ₁, Φ₂` agree (total
  probability: `μ (Φ⁻¹T) = ∑_s μ[Φ⁻¹T | k = s] μ(k = s)`).
* `mass_eq_of_map_eq`, `cond_map_eq_of_map_eq`: if `μ.map f₁ = ν.map f₂` and `k_i = ψ ∘ f_i`, the
  strata have equal masses and the conditional laws of `f₁, f₂` agree.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory ProbabilityTheory Set

variable {Ω₁ Ω₂ F ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace F]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω₁} {ν : Measure Ω₂} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem measure_eq_sum_cond {k : Ω₁ → ι} (hk : Measurable k) {B : Set Ω₁} :
    μ B = ∑ s, μ[B | k ⁻¹' {s}] * μ (k ⁻¹' {s}) := by
  have h := sum_measure_preimage_singleton (μ := μ.restrict B) (Finset.univ : Finset ι)
    (f := k) fun s _ => hk (measurableSet_singleton s)
  rw [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [cond_mul_eq_inter (hk (measurableSet_singleton s)), Measure.restrict_apply
    (hk (measurableSet_singleton s)), inter_comm]

theorem map_eq_of_cond_strata {k₁ : Ω₁ → ι} {k₂ : Ω₂ → ι} (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) {Φ₁ : Ω₁ → F} {Φ₂ : Ω₂ → F} (hΦ₁ : Measurable Φ₁)
    (hΦ₂ : Measurable Φ₂) (hmass : ∀ s, μ (k₁ ⁻¹' {s}) = ν (k₂ ⁻¹' {s}))
    (hcond : ∀ s, μ (k₁ ⁻¹' {s}) ≠ 0 →
      (μ[|k₁ ⁻¹' {s}]).map Φ₁ = (ν[|k₂ ⁻¹' {s}]).map Φ₂) :
    μ.map Φ₁ = ν.map Φ₂ := by
  ext T hT
  rw [Measure.map_apply hΦ₁ hT, Measure.map_apply hΦ₂ hT, measure_eq_sum_cond hk₁,
    measure_eq_sum_cond hk₂]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← hmass s]
  by_cases h0 : μ (k₁ ⁻¹' {s}) = 0
  · rw [h0, mul_zero, mul_zero]
  · have := congrArg (fun m : Measure F => m T) (hcond s h0)
    simp only [Measure.map_apply hΦ₁ hT, Measure.map_apply hΦ₂ hT] at this
    rw [this]

variable {E : Type*} [MeasurableSpace E]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure μ]
  [IsFiniteMeasure ν] in
theorem mass_eq_of_map_eq {f₁ : Ω₁ → E} {f₂ : Ω₂ → E} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (h : μ.map f₁ = ν.map f₂) {S : Set E} (hS : MeasurableSet S) :
    μ (f₁ ⁻¹' S) = ν (f₂ ⁻¹' S) := by
  rw [← Measure.map_apply hf₁ hS, ← Measure.map_apply hf₂ hS, h]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure μ]
  [IsFiniteMeasure ν] in
theorem cond_map_eq_of_map_eq {f₁ : Ω₁ → E} {f₂ : Ω₂ → E} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (h : μ.map f₁ = ν.map f₂) {S : Set E} (hS : MeasurableSet S) :
    (μ[|f₁ ⁻¹' S]).map f₁ = (ν[|f₂ ⁻¹' S]).map f₂ := by
  ext B hB
  rw [Measure.map_apply hf₁ hB, Measure.map_apply hf₂ hB, cond_apply (hf₁ hS),
    cond_apply (hf₂ hS), ← preimage_inter, ← preimage_inter,
    mass_eq_of_map_eq hf₁ hf₂ h hS, mass_eq_of_map_eq hf₁ hf₂ h (hS.inter hB)]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
