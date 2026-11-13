module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pathwise integrals of progressive processes are adapted)

Raw filtration `𝓖 : Filtration ℝ≥0 m₀`, no completeness.

* `stronglyMeasurable_integral_of_progressive`: for a strongly progressive real process `f`,
  `ω ↦ ∫_{(0,t]} f_s(ω) ds` is `𝓖_t`-strongly measurable for **every** `ω` (Fubini on
  `[0, t] × Ω` with the σ-algebra `𝓑 ⊗ 𝓖_t`); the Bochner integral is `0` on paths that are not
  integrable, which does not affect measurability.
* `le_of_le_hitTime_Ici`: on a continuous real path, before the
  hitting time of `[c, ∞)` the path is `≤ c` (when it starts below `c`).
* `tendsto_hitTime_Ici_top`: on a continuous real path, the hitting times of `[m, ∞)` tend to `⊤`.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}

/-- Auxiliary form of `stronglyMeasurable_integral_of_progressive` for the ambient σ-algebra. -/
theorem stronglyMeasurable_integral_of_prod {Ω' : Type*} [MeasurableSpace Ω'] {f : ℝ≥0 → Ω' → ℝ}
    (t : ℝ≥0) (hf : StronglyMeasurable fun p : Set.Iic t × Ω' => f p.1 p.2) :
    StronglyMeasurable (fun ω => ∫ s in Ioc (0 : ℝ) t, f s.toNNReal ω) := by
  set c : ℝ → Set.Iic t := fun s => ⟨min s.toNNReal t, min_le_right _ _⟩
  have hc : Measurable c := (measurable_real_toNNReal.min measurable_const).subtype_mk
  have hg : Measurable (fun p : ℝ × Ω' => (c p.1, p.2)) :=
    (hc.comp measurable_fst).prodMk measurable_snd
  have hF := hf.comp_measurable hg
  have hI := StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) t)) hF
  convert hI using 1
  funext ω
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hst : s.toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]; exact hs.2
  simp only [Function.comp, c, min_eq_left hst]

/-- **Pathwise integrals of strongly progressive processes are adapted.** -/
theorem stronglyMeasurable_integral_of_progressive {f : ℝ≥0 → Ω → ℝ}
    (hf : IsStronglyProgressive 𝓖 f) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] (fun ω => ∫ s in Ioc (0 : ℝ) t, f s.toNNReal ω) :=
  @stronglyMeasurable_integral_of_prod Ω (𝓖 t) f t (hf t)

/-- On a continuous real path starting below `c` (`Y 0 ω ≤ c`), the path stays `≤ c` up to the
hitting time of `[c, ∞)`. -/
theorem le_of_le_hitTime_Ici {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hY : Continuous fun t => Y t ω)
    {c : ℝ} (h0 : Y 0 ω ≤ c) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ hitTime (Ici c) Y ω) :
    Y t ω ≤ c := by
  have hlt : ∀ s : ℝ≥0, s < t → Y s ω < c := by
    intro s hs
    by_contra h
    push Not at h
    have : hitTime (Ici c) Y ω ≤ s := iInf₂_le s (show Y s ω ∈ Ici c from h)
    exact absurd (ht.trans this) (not_le.2 (WithTop.coe_lt_coe.2 hs))
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
  · rw [← h]; exact h0
  · have hne : (𝓝[<] t).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' (a := t) ⟨0, h⟩]; exact mem_Iic.2 le_rfl
    have hev : ∀ᶠ s in 𝓝[<] t, Y s ω ≤ c := by
      filter_upwards [self_mem_nhdsWithin] with s hs using (hlt s hs).le
    exact le_of_tendsto (x := 𝓝[<] t) ((hY.tendsto t).mono_left nhdsWithin_le_nhds) hev

/-- On a continuous real path the hitting times of `[m, ∞)` tend to `⊤`. -/
theorem tendsto_hitTime_Ici_top {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hY : Continuous fun t => Y t ω) :
    Tendsto (fun m : ℕ => hitTime (Ici (m : ℝ)) Y ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).exists_bound_of_continuousOn
    (f := fun t => Y t ω) hY.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop m] with k hk
  have hk' : M < k := hm.trans_le (by exact_mod_cast hk)
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one T)) (le_iInf₂ fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  have hs' : s ∈ Icc (0 : ℝ≥0) (T + 1) := ⟨zero_le, (WithTop.coe_lt_coe.1 hlt).le⟩
  have := hM s hs'
  rw [Real.norm_eq_abs] at this
  have h2 : (k : ℝ) ≤ Y s ω := hs
  linarith [le_abs_self (Y s ω)]

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
