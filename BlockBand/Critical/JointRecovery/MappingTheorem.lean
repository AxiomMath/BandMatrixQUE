module

public import Mathlib

/-!
# A continuous mapping theorem within a full-measure set

`tendsto_map_of_continuousWithinAt`: if probability measures `μ_i ⇒ μ` all give full mass to `S`
and `f` is measurable and continuous within `S` at `μ`-a.e. point, then `f_# μ_i ⇒ f_# μ`; with
its integral form for bounded measurable functions and the convergence of the Dirac products
`δ_{t_i} ⊗ μ_i ⇒ δ_t ⊗ μ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The closure of `f ⁻¹' F ∩ S` (`F` closed) gains only points where `f` is not continuous
within `S`. Deterministic; no measure. -/
theorem closure_preimage_inter_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (S : Set X) {F : Set Y} (hF : IsClosed F) :
    closure (f ⁻¹' F ∩ S) ⊆ f ⁻¹' F ∪ {x | ¬ ContinuousWithinAt f S x} := by
  intro x hx
  by_cases hc : ContinuousWithinAt f S x
  · left
    have h1 : f x ∈ closure (f '' (f ⁻¹' F ∩ S)) :=
      (hc.mono inter_subset_right).mem_closure_image hx
    have h2 : f '' (f ⁻¹' F ∩ S) ⊆ F := by
      rintro y ⟨z, hz, rfl⟩
      exact hz.1
    exact hF.closure_eq ▸ closure_mono h2 h1
  · exact Or.inr hc

/-- **Continuous mapping theorem within a full-measure set.** Law: probability measures
`μs i ⇒ μ` on `X` along a countably generated filter. If every `μs i` gives full mass to `S`
and `f` is measurable and continuous within `S` at `μ`-a.e. point, then
`(μs i).map f ⇒ μ.map f`. No uniformity. -/
theorem tendsto_map_of_continuousWithinAt {X Y ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {L : Filter ι} [L.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} {f : X → Y} {S : Set X}
    (hμ : Tendsto μs L (𝓝 μ)) (hf : Measurable f)
    (hS : ∀ i, (μs i : Measure X) Sᶜ = 0)
    (hcont : ∀ᵐ x ∂(μ : Measure X), ContinuousWithinAt f S x) :
    Tendsto (fun i => (μs i).map f) L (𝓝 (μ.map f)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have hmap (ρ : ProbabilityMeasure X) :
      ((ρ.map f : ProbabilityMeasure Y) : Measure Y) F = (ρ : Measure X) (f ⁻¹' F) :=
    Measure.map_apply hf hF.measurableSet
  simp_rw [hmap]
  have hnull : (μ : Measure X) {x | ¬ ContinuousWithinAt f S x} = 0 := by
    rw [← ae_iff]
    simpa only [not_not] using hcont
  have hle (i : ι) : (μs i : Measure X) (f ⁻¹' F) ≤
      (μs i : Measure X) (closure (f ⁻¹' F ∩ S)) := by
    calc (μs i : Measure X) (f ⁻¹' F)
        ≤ (μs i : Measure X) (f ⁻¹' F ∩ S) + (μs i : Measure X) (f ⁻¹' F \ S) :=
          measure_le_inter_add_sdiff _ _ _
      _ ≤ (μs i : Measure X) (closure (f ⁻¹' F ∩ S)) + (μs i : Measure X) Sᶜ :=
          add_le_add (measure_mono subset_closure) (measure_mono (sdiff_subset_compl _ _))
      _ = (μs i : Measure X) (closure (f ⁻¹' F ∩ S)) := by rw [hS i, add_zero]
  calc limsup (fun i => (μs i : Measure X) (f ⁻¹' F)) L
      ≤ limsup (fun i => (μs i : Measure X) (closure (f ⁻¹' F ∩ S))) L :=
        limsup_le_limsup (.of_forall hle)
    _ ≤ (μ : Measure X) (closure (f ⁻¹' F ∩ S)) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ ≤ (μ : Measure X) (f ⁻¹' F ∪ {x | ¬ ContinuousWithinAt f S x}) :=
        measure_mono (closure_preimage_inter_subset f S hF)
    _ ≤ (μ : Measure X) (f ⁻¹' F) + (μ : Measure X) {x | ¬ ContinuousWithinAt f S x} :=
        measure_union_le _ _
    _ = (μ : Measure X) (f ⁻¹' F) := by rw [hnull, add_zero]

/-- The clamp `y ↦ max (-C) (min C y)` as a bounded continuous real function. -/
def clampBCF (C : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max (-|C|) (min |C| y), by fun_prop⟩ (2 * |C|) (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : |max (-|C|) (min |C| x)| ≤ |C| := abs_le.mpr ⟨le_max_left _ _,
        max_le (by linarith [abs_nonneg C]) (min_le_left _ _)⟩
      have h2 : |max (-|C|) (min |C| y)| ≤ |C| := abs_le.mpr ⟨le_max_left _ _,
        max_le (by linarith [abs_nonneg C]) (min_le_left _ _)⟩
      calc |max (-|C|) (min |C| x) - max (-|C|) (min |C| y)|
          ≤ |max (-|C|) (min |C| x)| + |max (-|C|) (min |C| y)| := abs_sub _ _
        _ ≤ 2 * |C| := by linarith)

theorem clampBCF_apply_of_abs_le {C y : ℝ} (hy : |y| ≤ C) : clampBCF C y = y := by
  have hC : |C| = C := abs_of_nonneg ((abs_nonneg y).trans hy)
  simp only [clampBCF, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, hC]
  rw [min_eq_right (abs_le.mp hy).2, max_eq_right (abs_le.mp hy).1]

/-- **Integral form.** Under the hypotheses of `tendsto_map_of_continuousWithinAt`, for a
measurable `h : X → ℝ` bounded by `C` everywhere, `∫ h dμs i → ∫ h dμ`. -/
theorem tendsto_integral_of_continuousWithinAt {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {L : Filter ι} [L.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} {h : X → ℝ} {S : Set X}
    (hμ : Tendsto μs L (𝓝 μ)) (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hS : ∀ i, (μs i : Measure X) Sᶜ = 0)
    (hcont : ∀ᵐ x ∂(μ : Measure X), ContinuousWithinAt h S x) :
    Tendsto (fun i => ∫ x, h x ∂(μs i : Measure X)) L (𝓝 (∫ x, h x ∂(μ : Measure X))) := by
  have hmap := tendsto_map_of_continuousWithinAt hμ hh hS hcont
  have key := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap (clampBCF C)
  have hrw (ρ : ProbabilityMeasure X) :
      ∫ y, clampBCF C y ∂((ρ.map h : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫ x, h x ∂(ρ : Measure X) := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map hh.aemeasurable
      (clampBCF C).continuous.aestronglyMeasurable]
    exact integral_congr_ae (.of_forall fun x => clampBCF_apply_of_abs_le (hC x))
  simpa only [hrw] using key

/-- **Dirac product in a parameter.** If `t i → t` and `μs i ⇒ μ`, then
`δ_{t i} ⊗ μs i ⇒ δ_t ⊗ μ`. Spaces second countable and pseudo-metrizable (as required by
Mathlib's `ProbabilityMeasure.continuous_prod`). -/
theorem tendsto_diracProba_prod {T X ι : Type*}
    [MeasurableSpace T] [TopologicalSpace T] [OpensMeasurableSpace T]
    [SecondCountableTopology T] [TopologicalSpace.PseudoMetrizableSpace T]
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] [TopologicalSpace.PseudoMetrizableSpace X]
    {L : Filter ι} {ts : ι → T} {t : T} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (ht : Tendsto ts L (𝓝 t)) (hμ : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i => (diracProba (ts i)).prod (μs i)) L (𝓝 ((diracProba t).prod μ)) := by
  have hpair : Tendsto (fun i => (diracProba (ts i), μs i)) L (𝓝 (diracProba t, μ)) :=
    ((continuous_diracProba.tendsto t).comp ht).prodMk_nhds hμ
  exact (ProbabilityMeasure.continuous_prod.tendsto _).comp hpair

/-- Integral against `δ_t ⊗ μ` is integration of the section at `t`. -/
theorem integral_diracProba_prod {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [MeasurableSingletonClass T] (t : T) (μ : ProbabilityMeasure X) {h : T × X → ℝ}
    (hh : Measurable h) :
    ∫ p, h p ∂((diracProba t).prod μ : Measure (T × X)) = ∫ x, h (t, x) ∂(μ : Measure X) := by
  change ∫ p, h p ∂((Measure.dirac t).prod (μ : Measure X)) = _
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    hh.aestronglyMeasurable]

/-- The section `{t} × S` has full `δ_t ⊗ μ` mass as soon as `S` has full `μ` mass. -/
theorem diracProba_prod_compl_eq_zero {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [MeasurableSingletonClass T] (t : T) (μ : ProbabilityMeasure X) {S : Set (T × X)}
    (hSm : MeasurableSet S) (hS : (μ : Measure X) {x | (t, x) ∉ S} = 0) :
    ((diracProba t).prod μ : Measure (T × X)) Sᶜ = 0 := by
  change ((Measure.dirac t).prod (μ : Measure X)) Sᶜ = 0
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hSm.compl]
  exact hS

end BlockBand.Critical.JointRecovery
