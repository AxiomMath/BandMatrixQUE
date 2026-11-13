module

public import BlockBand.SourceProcess.ComplexSplit.Interface

/-!
# Generic one-time-law lemmas

* `map_eq_of_forall_lt`: two a.s. continuous processes (values in a Borel, pseudo-metrizable
  space, finite measures) whose one-time laws agree at every time `t < u`, `u > 0`, have equal
  laws at `u` (dominated convergence on bounded continuous tests along `t ↑ u`, then
  `ext_of_forall_integral_eq_of_IsFiniteMeasure`);
* `map_comp_eq`: equal laws are preserved by a measurable map.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUniqueSegment

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Generic

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace.PseudoMetrizableSpace Y]

omit [TopologicalSpace.PseudoMetrizableSpace Y] in
/-- Dominated convergence for a bounded continuous test along a.s. continuous paths. -/
theorem tendsto_integral_bcf {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → Y} (hm : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) (f : BoundedContinuousFunction Y ℝ)
    (u : ℝ≥0) :
    Tendsto (fun t => ∫ ω, f (X t ω) ∂Q) (𝓝[<] u) (𝓝 (∫ ω, f (X u ω) ∂Q)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun t =>
      (f.continuous.measurable.comp (hm t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun ω => f.norm_coe_le_norm _
  · filter_upwards [hc] with ω hω
    exact (f.continuous.tendsto _).comp ((hω.tendsto u).mono_left nhdsWithin_le_nhds)

/-- **Left limits of laws.** If two a.s. continuous processes have equal one-time laws at all
times before `u > 0`, they have equal laws at `u`. -/
theorem map_eq_of_forall_lt {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsFiniteMeasure Q₁] [IsFiniteMeasure Q₂]
    {X₁ : ℝ≥0 → Ω₁ → Y} {X₂ : ℝ≥0 → Ω₂ → Y}
    (hm₁ : ∀ t, Measurable (X₁ t)) (hm₂ : ∀ t, Measurable (X₂ t))
    (hc₁ : ∀ᵐ ω ∂Q₁, Continuous fun t => X₁ t ω) (hc₂ : ∀ᵐ ω ∂Q₂, Continuous fun t => X₂ t ω)
    {u : ℝ≥0} (hu : 0 < u) (heq : ∀ t < u, Q₁.map (X₁ t) = Q₂.map (X₂ t)) :
    Q₁.map (X₁ u) = Q₂.map (X₂ u) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hf : ∀ (μ : Measure Y), AEStronglyMeasurable (fun y => f y) μ :=
    fun μ => f.continuous.measurable.aestronglyMeasurable
  have hI : ∀ t, ∫ ω, f (X₁ t ω) ∂Q₁ = ∫ y, f y ∂(Q₁.map (X₁ t)) := fun t =>
    (integral_map (hm₁ t).aemeasurable (hf _)).symm
  have hJ : ∀ t, ∫ ω, f (X₂ t ω) ∂Q₂ = ∫ y, f y ∂(Q₂.map (X₂ t)) := fun t =>
    (integral_map (hm₂ t).aemeasurable (hf _)).symm
  rw [← hI, ← hJ]
  have : NeBot (𝓝[<] u) := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  have h₁ := tendsto_integral_bcf hm₁ hc₁ f u
  have h₂ := tendsto_integral_bcf hm₂ hc₂ f u
  refine tendsto_nhds_unique (h₁.congr' ?_) h₂
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hI, hJ, heq t ht]

end Generic

/-- Equal laws are preserved by a measurable map. -/
theorem map_comp_eq {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} {X₁ : Ω₁ → Y} {X₂ : Ω₂ → Y}
    (hm₁ : Measurable X₁) (hm₂ : Measurable X₂) {φ : Y → Z} (hφ : Measurable φ)
    (heq : Q₁.map X₁ = Q₂.map X₂) :
    Q₁.map (fun ω => φ (X₁ ω)) = Q₂.map (fun ω => φ (X₂ ω)) := by
  change Q₁.map (φ ∘ X₁) = Q₂.map (φ ∘ X₂)
  rw [← Measure.map_map hφ hm₁, ← Measure.map_map hφ hm₂, heq]

end BlockBand.SourceProcess.ComplexUniqueSegment
