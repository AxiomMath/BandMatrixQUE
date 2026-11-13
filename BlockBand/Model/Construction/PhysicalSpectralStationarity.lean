module
public import BlockBand.Model.Construction.BoundedEventIntegral
public import BlockBand.Model.Construction.MarkedTranslationLaw
public import BlockBand.Model.Construction.GaussianTranslationPhysical
public import BlockBand.Asymptotics.CriticalSequence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite and subsequential spectral stationarity

The finite physical marked law is almost invariant under global spectral translation, with an
error that vanishes along a critical sequence; hence every weak subsequential limit has
translation-invariant bounded continuous expectations.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Filter
open scoped Topology

variable {p : Parameters}

theorem globalMarkedTranslationLaw_canonical (model : p.GaussianRingModel) (E t : ℝ) :
    globalMarkedTranslationLaw t (model.canonicalPhysicalMarkedLaw E) =
      model.translatedCanonicalPhysicalMarkedLaw E t := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (globalMarkedTranslation t)
    (Measure.map (physicalOrderedMarkedConfig p E) (model.law : Measure p.SiteMatrix)) =
      Measure.map (gaussianTranslatedCanonicalMarkedConfig p E t)
        (model.law : Measure p.SiteMatrix)
  rw [Measure.map_map (measurable_globalMarkedTranslation t)
    (measurable_physicalOrderedMarkedConfig p E)]
  congr 1
  funext H
  exact globalMarkedTranslation_canonical p E t H

theorem canonicalPhysicalMarkedLaw_global_translation_integral_le
    (model : p.GaussianRingModel) (E t : ℝ) (hE : E^2 < 4)
    (f : BoundedContinuousFunction MarkedPointMeasure ℝ) :
    |(∫ ξ, f ξ ∂(model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure)) -
      (∫ ξ, f ξ ∂(globalMarkedTranslationLaw t (model.canonicalPhysicalMarkedLaw E) :
        Measure MarkedPointMeasure))| ≤
      2*‖f‖*min 1 (|t|/(Parameters.semicircleDensity E *
        Real.sqrt (2*Real.pi*p.c*(p.n : ℝ)))) := by
  rw [globalMarkedTranslationLaw_canonical]
  exact integral_signed_sub_le_of_event_bound _ _ f f.continuous.measurable
    ‖f‖ _ (norm_nonneg _) (fun ξ=>f.norm_coe_le_norm ξ)
    (model.canonicalPhysicalMarkedLaw_translation_event_le E
      (Parameters.semicircleDensity_pos_of_sq_lt_four E hE) t)

/-- The law of the canonical constructed physical realization, at every index. -/
def criticalPhysicalMarkedLaws {τ : ℝ} (s : CriticalSequence τ)
    (b E : ℝ) (hb : 0<b) (hb' : b<1/2) : ℕ → ProbabilityMeasure MarkedPointMeasure :=
  fun j => (constructFiniteRealization (s.parameters b hb hb' j)).markedLaw E

/-- Along a critical sequence `n → ∞`. -/
theorem criticalSequence_n_real_tendsto_atTop {τ : ℝ} (s : CriticalSequence τ) (hτ : 0<τ) :
    Tendsto (fun j => (s.n j : ℝ)) atTop atTop := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  apply tendsto_atTop.2
  intro B
  have hratio : ∀ᶠ j in atTop, τ/2 < (s.n j : ℝ)/(s.W j : ℝ) :=
    s.ratio_tendsto (Ioi_mem_nhds (by linarith : τ/2<τ))
  have hwidth : ∀ᶠ j in atTop, 2*B/τ ≤ (s.W j : ℝ) :=
    hW (eventually_ge_atTop _)
  filter_upwards [hratio,hwidth] with j hj hw
  have h1 := (lt_div_iff₀ (show (0 : ℝ)<s.W j from Nat.cast_pos.mpr (s.W_pos j))).mp hj
  have h2 := (div_le_iff₀ hτ).mp hw
  linarith

/-- The uncapped physical translation error vanishes at critical scaling. -/
theorem criticalSequence_translation_error_tendsto_zero {τ : ℝ}
    (s : CriticalSequence τ) (hτ : 0<τ) (b E t : ℝ)
    (hb : 0<b) (hb' : b<1/2) (hE : E^2<4) :
    Tendsto (fun j => |t|/(Parameters.semicircleDensity E *
      Real.sqrt (2*Real.pi*(s.parameters b hb hb' j).c*(s.n j : ℝ))))
      atTop (𝓝 0) := by
  let k : ℝ := 2*Real.pi*(s.parameters b hb hb' 0).c
  have hk : 0<k := by dsimp [k];positivity [(s.parameters b hb hb' 0).c_pos]
  have hA : Tendsto (fun j => k*(s.n j : ℝ)) atTop atTop :=
    (criticalSequence_n_real_tendsto_atTop s hτ).const_mul_atTop hk
  have hsqrt : Tendsto (fun j => Real.sqrt (k*(s.n j : ℝ))) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [hA (eventually_ge_atTop (B^2))] with j hj
    have hsq := Real.sqrt_le_sqrt hj
    rw [Real.sqrt_sq_eq_abs] at hsq
    exact (le_abs_self B).trans hsq
  have hden := hsqrt.const_mul_atTop (Parameters.semicircleDensity_pos_of_sq_lt_four E hE)
  have hi := (tendsto_inv_atTop_zero.comp hden).const_mul |t|
  simpa only [k, CriticalSequence.parameters, Parameters.c, div_eq_mul_inv, mul_zero, Function.comp_def] using hi

/-- Every weak subsequential marked limit has translation-invariant real bounded-test
expectations, derived from the physical finite law and critical scaling. -/
theorem criticalSequence_marked_weakLimit_spectral_integral_eq {τ : ℝ}
    (s : CriticalSequence τ) (hτ : 0<τ) (b E : ℝ) (hb : 0<b) (hb' : b<1/2)
    (hE : E^2<4) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>criticalPhysicalMarkedLaws s b E hb hb' (φ j)) atTop (𝓝 ν))
    (t : ℝ) (f : BoundedContinuousFunction MarkedPointMeasure ℝ) :
    (∫ ξ, f ξ ∂(ν : Measure MarkedPointMeasure)) =
      ∫ ξ, f ξ ∂(globalMarkedTranslationLaw t ν : Measure MarkedPointMeasure) := by
  let laws := fun j=>criticalPhysicalMarkedLaws s b E hb hb' (φ j)
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  have ht := tendsto_globalMarkedTranslationLaw t laws ν hlim
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht) f
  have hd := h1.sub h2
  have he := (criticalSequence_translation_error_tendsto_zero s hτ b E t hb hb' hE).comp
    hφ.tendsto_atTop
  have he' : Tendsto (fun j => (2*‖f‖)*(|t|/(Parameters.semicircleDensity E *
      Real.sqrt (2*Real.pi*(s.parameters b hb hb' (φ j)).c*(s.n (φ j) : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using he.const_mul (2*‖f‖)
  have hzero : Tendsto (fun j =>
      |(∫ ξ, f ξ ∂(laws j : Measure MarkedPointMeasure)) -
        (∫ ξ, f ξ ∂(globalMarkedTranslationLaw t (laws j) : Measure MarkedPointMeasure))|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _=>abs_nonneg _) _ he'
    intro j
    have h := canonicalPhysicalMarkedLaw_global_translation_integral_le
      (s.parameters b hb hb' (φ j)).constructGaussianRingModel E t hE f
    change _ ≤ _ at h
    change _ ≤ _
    have hc : 0 ≤ 2*‖f‖ := by positivity
    exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hc)
  have heq := tendsto_nhds_unique hd.abs hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp heq)

end BlockBand.Model.Construction
