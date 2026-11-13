module
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Almost sure limits of identically distributed sequences

A tool for the law argument of uniqueness.

**`map_eq_of_tendsto_ae`**: on two finite measure spaces, if `f¹_n → g¹` and `f²_n → g²`
almost surely in a pseudo-metrizable Borel space `E` and `law(f¹_n) = law(f²_n)` for every
`n`, then `law(g¹) = law(g²)` (bounded continuous test functions, dominated convergence,
`ext_of_forall_lintegral_eq_of_IsFiniteMeasure`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem tendsto_lintegral_bcf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : ℕ → Ω → E} {g : Ω → E} (hf : ∀ n, AEMeasurable (f n) P)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) (φ : BoundedContinuousFunction E ℝ≥0) :
    Tendsto (fun n => ∫⁻ x, (φ x : ℝ≥0∞) ∂P.map (f n)) atTop
      (𝓝 (∫⁻ x, (φ x : ℝ≥0∞) ∂P.map g)) := by
  have hg := aemeasurable_of_tendsto_metrizable_ae' hf h
  have hφ : Measurable fun x => (φ x : ℝ≥0∞) := φ.continuous.measurable.coe_nnreal_ennreal
  simp_rw [lintegral_map' hφ.aemeasurable (hf _), lintegral_map' hφ.aemeasurable hg]
  obtain ⟨C, hC⟩ := φ.isBounded_range.bddAbove
  refine tendsto_lintegral_of_dominated_convergence' (fun _ => (C : ℝ≥0∞))
    (fun n => hφ.comp_aemeasurable (hf n)) (fun n => Eventually.of_forall fun ω => ?_)
    (by simp [lintegral_const, ENNReal.mul_eq_top]) ?_
  · exact ENNReal.coe_le_coe.2 (hC ⟨f n ω, rfl⟩)
  · filter_upwards [h] with ω hω
    exact (ENNReal.continuous_coe.comp φ.continuous).continuousAt.tendsto.comp hω

/-- **Equal laws pass to almost sure limits.** -/
theorem map_eq_of_tendsto_ae {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsFiniteMeasure P₁] [IsFiniteMeasure P₂]
    [HasOuterApproxClosed E] {f₁ : ℕ → Ω₁ → E} {f₂ : ℕ → Ω₂ → E} {g₁ : Ω₁ → E} {g₂ : Ω₂ → E}
    (hf₁ : ∀ n, AEMeasurable (f₁ n) P₁) (hf₂ : ∀ n, AEMeasurable (f₂ n) P₂)
    (h₁ : ∀ᵐ ω ∂P₁, Tendsto (fun n => f₁ n ω) atTop (𝓝 (g₁ ω)))
    (h₂ : ∀ᵐ ω ∂P₂, Tendsto (fun n => f₂ n ω) atTop (𝓝 (g₂ ω)))
    (heq : ∀ n, P₁.map (f₁ n) = P₂.map (f₂ n)) : P₁.map g₁ = P₂.map g₂ := by
  refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun φ => ?_
  refine tendsto_nhds_unique (tendsto_lintegral_bcf hf₁ h₁ φ) ?_
  simp_rw [heq]
  exact tendsto_lintegral_bcf hf₂ h₂ φ

end BlockBand.SourceProcess.Stochastic.Uniqueness
