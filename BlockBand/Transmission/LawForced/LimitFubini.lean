module

public import BlockBand.Transmission.LawDuality.BorelGiry

/-!
# Fubini for a bounded drift along a continuous random-measure path

`W`-free. A version of `Generator.limit_fubini` for a process with values in
`FiniteMeasure [0,1]` and a *bounded* drift `G(u, ν)` jointly continuous in `(u, ν)`
(`continuousAt_ratioDrift`, `exists_bound_ratioDrift`), so no moment input.

**`limit_fubini_bdd`**: for `0 < s ≤ t`, a bounded measurable `ψ`, measurable marginals
`μ_u` (`u > 0`) and a.s. continuous paths on `(0, ∞)`:
`ω ↦ ∫_s^t G(u, μ_u ω) du` is integrable, `E[ψ ∫_s^t G] = ∫_s^t E[ψ G(u, μ_u)] du`, and the
inner function is interval integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Topology Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Fubini on the limit, bounded jointly continuous drift.** -/
theorem limit_fubini_bdd {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hmeas : ∀ t, 0 < t → Measurable (μ t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0))
    {G : ℝ → FiniteMeasure unitInterval → ℝ}
    (hG : ∀ u ν, ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => G q.1 q.2) (u, ν))
    {C : ℝ} (hC : ∀ u ν, |G u ν| ≤ C) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {ψ : Ω → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ ω, |ψ ω| ≤ B) :
    Integrable (fun ω => ∫ u in s..t, G u (μ u ω)) P ∧
      ∫ ω, ψ ω * (∫ u in s..t, G u (μ u ω)) ∂P = ∫ u in s..t, ∫ ω, ψ ω * G u (μ u ω) ∂P ∧
      IntervalIntegrable (fun u => ∫ ω, ψ ω * G u (μ u ω) ∂P) MeasureTheory.volume s t := by
  have hGc : Continuous fun q : ℝ × FiniteMeasure unitInterval => G q.1 q.2 :=
    continuous_iff_continuousAt.mpr fun q => hG q.1 q.2
  set S := (toMeasurable P {ω | ¬ ContinuousOn (fun t => μ t ω) (Set.Ioi 0)})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hS : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]; simp only [hSdef, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq]
    rw [measure_toMeasurable]; exact ae_iff.mp hcont
  have hSgood : ∀ ω ∈ S, ContinuousOn (fun t => μ t ω) (Set.Ioi 0) := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  set cl : ℝ → ℝ := fun u => max s (min t u)
  have hcl : Continuous cl := by fun_prop
  have hcl_pos : ∀ u, 0 < cl u := fun u => lt_of_lt_of_le hs (le_max_left _ _)
  have hcl_eq : ∀ u ∈ Set.uIcc s t, cl u = u := by
    intro u hu
    rw [Set.uIcc_of_le hst] at hu
    simp only [cl, min_eq_right hu.2, max_eq_right hu.1]
  set F : ℝ → Ω → ℝ := fun u ω => S.indicator (fun ω => G (cl u) (μ (cl u) ω)) ω
  have hFc : ∀ ω, Continuous fun u => F u ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [F, Set.indicator_of_mem hω]
      have hpath : Continuous fun u => μ (cl u) ω :=
        (hSgood ω hω).comp_continuous hcl fun u => hcl_pos u
      exact hGc.comp (hcl.prodMk hpath)
    · simp only [F, Set.indicator_of_notMem hω]; exact continuous_const
  have hFm : ∀ u, Measurable (F u) := fun u =>
    ((hGc.comp (continuous_const.prodMk continuous_id)).measurable.comp
      (hmeas _ (hcl_pos u))).indicator hSm
  have hF2 : Measurable (Function.uncurry F) :=
    measurable_uncurry_of_continuous_of_measurable hFc hFm
  have hFb : ∀ u ω, |F u ω| ≤ max C 0 := by
    intro u ω
    by_cases hω : ω ∈ S
    · simp only [F, Set.indicator_of_mem hω]; exact (hC _ _).trans (le_max_left _ _)
    · simp only [F, Set.indicator_of_notMem hω, abs_zero]; exact le_max_right _ _
  have hint : ∀ {c : Ω → ℝ}, Measurable c → (∀ ω, |c ω| ≤ max B 1) →
      Integrable (Function.uncurry fun u ω => c ω * F u ω)
        ((volume.restrict (Set.uIoc s t)).prod P) := by
    intro c hc hcB
    have hmeas2 : Measurable (Function.uncurry fun u ω => c ω * F u ω) :=
      (hc.comp measurable_snd).mul hF2
    have : IsFiniteMeasure (volume.restrict (Set.uIoc s t)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    refine Integrable.of_bound (C := max B 1 * max C 0) hmeas2.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hcB _) (hFb _ _) (abs_nonneg _) (by positivity)
  have hψ' : ∀ ω, |ψ ω| ≤ max B 1 := fun ω => (hB ω).trans (le_max_left _ _)
  have h1 := hint hψ hψ'
  have h0 := hint (c := fun _ => (1 : ℝ)) measurable_const fun _ => by simp
  have hFω : ∀ᵐ ω ∂P, ∫ u in s..t, F u ω = ∫ u in s..t, G u (μ u ω) := by
    filter_upwards [hS] with ω hω
    refine intervalIntegral.integral_congr fun u hu => ?_
    simp only [F, Set.indicator_of_mem hω, hcl_eq u hu]
  have hFu : ∀ u ∈ Set.uIcc s t, ∫ ω, ψ ω * F u ω ∂P = ∫ ω, ψ ω * G u (μ u ω) ∂P := by
    intro u hu
    refine integral_congr_ae ?_
    filter_upwards [hS] with ω hω
    simp only [F, Set.indicator_of_mem hω, hcl_eq u hu]
  constructor
  · have := h0.integral_prod_right
    simp only [Function.uncurry_apply_pair, one_mul] at this
    refine (this.congr ?_)
    filter_upwards [hFω] with ω hω
    rw [← hω, intervalIntegral.integral_of_le hst, Set.uIoc_of_le hst]
  refine ⟨?_, ?_⟩
  · rw [← intervalIntegral.integral_congr hFu, intervalIntegral_integral_swap h1]
    refine integral_congr_ae ?_
    filter_upwards [hFω] with ω hω
    rw [intervalIntegral.integral_const_mul, hω]
  · have h2 := h1.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h2
    rw [intervalIntegrable_iff]
    exact IntegrableOn.congr_fun h2 (fun u hu => hFu u (Set.uIoc_subset_uIcc hu))
      measurableSet_uIoc

end BlockBand.Transmission.LawForced
