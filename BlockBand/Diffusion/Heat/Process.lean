module

public import BlockBand.Diffusion.Heat.Kernel

/-!
# Dynkin's formula and the approximate identity through the base diffusion

* `IsExBaseDiffusion.exists_chGoodVersion`: a version `W` of `Z` with **every** path continuous,
  in the strip and started at `z`, each `W t` measurable, and `W = Z` a.s. as paths.
* `ChGoodVersion.integral_comp`: `E[g(W_s)] = P_s g(z)` for `s > 0` (the transition
  law `IsExBaseDiffusion.map_eq_exKer`, with `mcKeanBackwardFacts_holds` and
  `timeMollifyDuality_holds`).
* `ChGoodVersion.dynkin`: `E f(W_t) = f(z) + E ∫_{(0,t]} 𝒟₀f(W_u) du` for `f ∈ C_c^∞(ℝ²)`
  (the martingale field of `IsExBaseDiffusion` at times `0 ≤ t`).
* `ChGoodVersion.integral_setIntegral_swap`: Fubini in `(ω, u)` for `g` measurable and bounded
  on the strip.
* `ch_tendsto_chP`: `P_s g(z) → g(z)` as `s → 0+` for `g` measurable, continuous on the strip and
  bounded there (dominated convergence along the continuous paths).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

section Process

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

/-- A version `W` of `Z` with all paths continuous, in the strip and started at `z`. -/
structure ChGoodVersion (P : Measure Ω) (z : ℝ × ℝ) (Z W : ℝ≥0 → Ω → ℝ × ℝ) : Prop where
  meas : ∀ t, Measurable (W t)
  cont : ∀ ω, Continuous fun t => W t ω
  strip : ∀ t ω, W t ω ∈ exBaseStrip
  start : ∀ ω, W 0 ω = z
  ae_eq : ∀ᵐ ω ∂P, ∀ t, W t ω = Z t ω

theorem IsExBaseDiffusion.exists_chGoodVersion (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hz : z ∈ exBaseStrip) : ∃ W, ChGoodVersion P z Z W := by
  classical
  set G : Set Ω := {ω | (Continuous fun t => Z t ω) ∧ (∀ t, Z t ω ∈ exBaseStrip) ∧ Z 0 ω = z}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := (h.paths.and h.start).mono fun ω hω => ⟨hω.1.1, hω.1.2, hω.2⟩
  set S : Set Ω := (toMeasurable P Gᶜ)ᶜ
  have hS : MeasurableSet S := (measurableSet_toMeasurable P _).compl
  have hSG : S ⊆ G := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable P _ hn)
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]
    have h0 : P Gᶜ = 0 := ae_iff.1 hG
    have : {a | ¬ a ∈ S} = toMeasurable P Gᶜ := by ext; simp [S]
    rw [this, measure_toMeasurable, h0]
  refine ⟨fun t ω => if ω ∈ S then Z t ω else z, ⟨fun t => ?_, fun ω => ?_, fun t ω => ?_,
    fun ω => ?_, hSae.mono fun ω hω t => by simp [hω]⟩⟩
  · exact Measurable.ite hS ((h.adapted t).mono (𝓖.le t) le_rfl) measurable_const
  · by_cases hω : ω ∈ S
    · simpa [hω] using (hSG hω).1
    · have : (fun t => if ω ∈ S then Z t ω else z) = fun _ => z := by funext t; simp [hω]
      rw [this]
      exact continuous_const
  · by_cases hω : ω ∈ S
    · simpa [hω] using (hSG hω).2.1 t
    · simpa [hω] using hz
  · by_cases hω : ω ∈ S
    · simpa [hω] using (hSG hω).2.2
    · simp [hω]

variable {W : ℝ≥0 → Ω → ℝ × ℝ}

theorem ChGoodVersion.measurable_uncurry (hW : ChGoodVersion P z Z W) :
    Measurable fun p : ℝ × Ω => W p.1.toNNReal p.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) ω => W s.toNNReal ω)
    (fun ω => (hW.cont ω).comp continuous_real_toNNReal) (fun _ => hW.meas _)

theorem ChGoodVersion.measurable_uncurry' (hW : ChGoodVersion P z Z W) :
    Measurable fun p : Ω × ℝ => W p.2.toNNReal p.1 :=
  hW.measurable_uncurry.comp measurable_swap

/-- `E[g(W_s)] = P_s g(z)` for `s > 0`. -/
theorem ChGoodVersion.integral_comp (hW : ChGoodVersion P z Z W)
    (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) {s : ℝ≥0}
    (hs : 0 < s) {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (W s ω) ∂P = chP D0 s g z := by
  have hZs : Measurable (Z s) := (h.adapted s).mono (𝓖.le s) le_rfl
  have hpm : Measurable fun z' => ENNReal.ofReal (exKernel D0 s z z') :=
    ((exKernel_measurable hD0).comp (f := fun z' : ℝ × ℝ => ((s : ℝ), z, z'))
      (by fun_prop)).ennreal_ofReal
  rw [integral_congr_ae (hW.ae_eq.mono fun ω hω => by rw [hω s]),
    ← integral_map hZs.aemeasurable hg.aestronglyMeasurable,
    h.map_eq_exKer hD0 hz (mcKeanBackwardFacts_holds D0 hD0) (timeMollifyDuality_holds D0 hD0) hs,
    exKer_apply hD0, integral_withDensity_eq_integral_toReal_smul hpm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exKernel_nonneg hD0 _ _ _), smul_eq_mul, chP]

/-- **Dynkin's formula** for smooth compactly supported tests, along the good version. -/
theorem ChGoodVersion.dynkin (hW : ChGoodVersion P z Z W) (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    ∫ ω, f (W t ω) ∂P =
      f z + ∫ ω, (∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (W u.toNNReal ω)) ∂P := by
  have := h.prob
  have hM := h.martingale f hf hfc
  have hZt : Measurable (Z t) := (h.adapted t).mono (𝓖.le t) le_rfl
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hfZ : Integrable (fun ω => f (Z t ω)) P :=
    Integrable.of_bound (hf.continuous.measurable.comp hZt).aestronglyMeasurable C
      (ae_of_all _ fun ω => hC _)
  have h0 : ∫ ω, (fun t ω => f (Z t ω) -
      ∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (Z u.toNNReal ω)) 0 ω ∂P = f z := by
    rw [integral_congr_ae (h.start.mono fun ω hω => by
      simp only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
        sub_zero]
      rw [hω])]
    simp
  have hMt := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hMt
  rw [h0] at hMt
  have hI : ∫ ω, (∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (Z u.toNNReal ω)) ∂P =
      ∫ ω, f (Z t ω) ∂P - f z := by
    rw [hMt, ← integral_sub hfZ (hM.integrable t)]
    congr 1
    funext ω
    ring
  have e1 : ∫ ω, f (W t ω) ∂P = ∫ ω, f (Z t ω) ∂P :=
    integral_congr_ae (hW.ae_eq.mono fun ω hω => by simp only [hω t])
  have e2 : ∫ ω, (∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (W u.toNNReal ω)) ∂P =
      ∫ ω, (∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (Z u.toNNReal ω)) ∂P :=
    integral_congr_ae (hW.ae_eq.mono fun ω hω => by simp_rw [hω])
  rw [e1, e2, hI]
  ring

/-- Fubini in `(ω, u)` for `g` measurable and bounded on the strip. -/
theorem ChGoodVersion.integral_setIntegral_swap (hW : ChGoodVersion P z Z W)
    [IsProbabilityMeasure P] {g : ℝ × ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ w ∈ exBaseStrip, |g w| ≤ C) (t : ℝ) :
    ∫ ω, (∫ u in Ioc (0 : ℝ) t, g (W u.toNNReal ω)) ∂P =
      ∫ u in Ioc (0 : ℝ) t, (∫ ω, g (W u.toNNReal ω) ∂P) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    ⟨by simp [Real.volume_Ioc]⟩
  refine integral_integral_swap (f := fun ω (u : ℝ) => g (W u.toNNReal ω)) ?_
  refine Integrable.of_bound (hg.comp hW.measurable_uncurry').aestronglyMeasurable C
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  exact hC _ (hW.strip _ _)

/-- `E[g(W_s)] → g(z)` as `s → 0+` for `g` continuous on the strip and bounded there. -/
theorem ChGoodVersion.tendsto_integral (hW : ChGoodVersion P z Z W) [IsProbabilityMeasure P]
    (hz : z ∈ exBaseStrip) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hgc : ContinuousOn g exBaseStrip) {C : ℝ} (hC : ∀ w ∈ exBaseStrip, |g w| ≤ C) :
    Tendsto (fun s : ℝ => ∫ ω, g (W s.toNNReal ω) ∂P) (𝓝[>] 0) (𝓝 (g z)) := by
  have hlim : ∫ ω, g z ∂P = g z := by simp
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun _ => (hg.comp (hW.meas _)).aestronglyMeasurable)
    (Eventually.of_forall fun _ => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hC _ (hW.strip _ _))
    (integrable_const C) (ae_of_all _ fun ω => ?_)
  have hp : Tendsto (fun s : ℝ => W s.toNNReal ω) (𝓝 0) (𝓝 z) := by
    have := ((hW.cont ω).comp continuous_real_toNNReal).tendsto 0
    simp only [Function.comp_def, Real.toNNReal_zero, hW.start ω] at this
    exact this
  have hp' : Tendsto (fun s : ℝ => W s.toNNReal ω) (𝓝[>] 0) (𝓝[exBaseStrip] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hp.mono_left nhdsWithin_le_nhds,
      Eventually.of_forall fun s => hW.strip _ _⟩
  exact (hgc z hz).tendsto.comp hp'

end Process

/-- **Approximate identity at `t = 0`**: `P_s g(z) → g(z)` as `s → 0+`, for `z` in the strip and
`g` measurable, continuous on the strip and bounded there. -/
theorem ch_tendsto_chP {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hgc : ContinuousOn g exBaseStrip) {C : ℝ}
    (hC : ∀ w ∈ exBaseStrip, |g w| ≤ C) :
    Tendsto (fun s : ℝ => chP D0 s g z) (𝓝[>] 0) (𝓝 (g z)) := by
  obtain ⟨Ω, m, 𝓖, P, Z, h⟩ := hasExBaseDiffusion D0 hD0 z hz
  obtain ⟨W, hW⟩ := h.exists_chGoodVersion hz
  have := h.prob
  refine (hW.tendsto_integral hz hg hgc hC).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  rw [hW.integral_comp h hD0 hz hs' hg, Real.coe_toNNReal _ (le_of_lt hs)]

end BlockBand.Diffusion
