module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.StopIdentity
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.PredSample
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import Mathlib.Topology.UrysohnsLemma
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Localization tools: a.s.-equal stopping times and cutoff extensions

**Stopping times changed on null sets.** `μ` is any measure on `ℝ × Ω` with
`μ ≪ dt|_{(0,T]} ⊗ Q` (`timeProbMeasure T Q`; e.g. the bracket measure `ν_T`).
* `stopSet_ae_eq`: `τ = τ'` `Q`-a.s. implies `[[0,τ]] = [[0,τ']]` `μ`-a.e. (`τ'` arbitrary).
* `predInd_stopSet_congr_ae`: two a.s.-equal raw stopping times give the same `predInd`;
  `predInd_stopSet_coeFn_ae`: the representative of `predInd (stopSet τ) H` is
  `1_{[[0,τ']]} H` `μ`-a.e.
* `contIntegral_predInd_stopSet_all_ae`: for `h : IsL2Integrator`, `Q` finite,
  `∫_0^v H 1{s ≤ τ} dN = Z_{v ∧ τ'}` a.s. for all `v` simultaneously.
* `exists_stopped_integral_hitTime`: for a closed `F` and an adapted a.s.-continuous `Y`, there is
  a raw stopping time `τ` (a.s. equal to `hitTime F Y`) with
  `∫_0^v H 1{s ≤ τ} dN = Z_{v ∧ hitTime F Y}` a.s. for all `v`, and representative
  `1{s ≤ hitTime F Y} H` `ν_T`-a.e.

**Cutoff extensions** (normal spaces, e.g. metric `E`): `U` open, `W` closed, `W ⊆ U`.
* `exists_cutoff`: a continuous `χ : E → [0,1]` with `χ = 1` on `W`, `χ = 0` off `U`, such that
  `χ f` is continuous on `E` for every `f` continuous on `U` (`χ` vanishes near `Uᶜ`).
* `exists_continuous_psd_extension`: a coefficient matrix `φ` continuous on `U` and PSD on `U`
  has an everywhere continuous, everywhere PSD extension `ψ = χ φ` agreeing with `φ` on `W`,
  `|ψ_{ij}| ≤ |φ_{ij}|`, symmetric where `φ` is.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-!
### Stopping times changed on null sets
-/

/-- `τ = τ'` a.s. implies `stopSet τ = stopSet τ'` `μ`-a.e. for `μ ≪ dt ⊗ Q`. -/
theorem stopSet_ae_eq [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    (hμ : μ ≪ timeProbMeasure T Q) {τ τ' : Ω → WithTop ℝ≥0} (hττ : τ =ᵐ[Q] τ') :
    stopSet τ =ᵐ[μ] stopSet τ' := by
  filter_upwards [hμ.ae_le (ae_timeProb_snd (T := T) hττ)] with p hp
  rw [mem_stopSet, mem_stopSet, hp]

/-- Two a.s.-equal raw stopping times define the same stopped integrand. -/
theorem predInd_stopSet_congr_ae [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    (hμ : μ ≪ timeProbMeasure T Q) {τ τ' : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτ' : IsStoppingTime 𝓖 τ') (hττ : τ =ᵐ[Q] τ') (H : PredL2 𝓖 μ) :
    predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H =
      predInd 𝓖 (stopSet τ') (measurableSet_stopSet 𝓖 hτ') H :=
  predInd_congr 𝓖 _ _ (stopSet_ae_eq hμ hττ) H

/-- The representative of `predInd (stopSet τ) H` is `1_{[[0,τ']]} H` for any `τ' = τ` a.s. -/
theorem predInd_stopSet_coeFn_ae [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    (hμ : μ ≪ timeProbMeasure T Q) {τ τ' : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hττ : τ =ᵐ[Q] τ') (H : PredL2 𝓖 μ) :
    (((predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H : PredL2 𝓖 μ) : Lp ℝ 2 μ) :
      ℝ × Ω → ℝ) =ᵐ[μ] (stopSet τ').indicator ((H : Lp ℝ 2 μ) : ℝ × Ω → ℝ) := by
  filter_upwards [predInd_coeFn 𝓖 _ (measurableSet_stopSet 𝓖 hτ) H, stopSet_ae_eq hμ hττ]
    with p h1 h2
  rw [h1]
  by_cases hp : p ∈ stopSet τ
  · have hp' : p ∈ stopSet τ' := by
      have : (p ∈ stopSet τ) = (p ∈ stopSet τ') := h2
      rwa [← this]
    rw [indicator_of_mem hp, indicator_of_mem hp']
  · have hp' : p ∉ stopSet τ' := by
      have : (p ∈ stopSet τ) = (p ∈ stopSet τ') := h2
      rwa [← this]
    rw [indicator_of_notMem hp, indicator_of_notMem hp']

theorem stoppedProcess_congr_ae {X : ℝ≥0 → Ω → ℝ} {τ τ' : Ω → WithTop ℝ≥0}
    (hττ : τ =ᵐ[Q] τ') : ∀ᵐ ω ∂Q, ∀ v, stoppedProcess X τ v ω = stoppedProcess X τ' v ω := by
  filter_upwards [hττ] with ω hω v
  simp only [stoppedProcess, hω]

namespace IsL2Integrator

variable [IsFiniteMeasure Q] {N α : ℝ≥0 → Ω → ℝ} (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0)
  (H : PredL2 𝓖 (bracketMeasure Q α T))

/-- **Stopping identity with an a.s.-equal stopping time** `τ'` (e.g. an exit time). -/
theorem contIntegral_predInd_stopSet_all_ae {τ τ' : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hττ : τ =ᵐ[Q] τ') :
    ∀ᵐ ω ∂Q, ∀ v, h.contIntegral T (predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H) v ω =
      stoppedProcess (h.contIntegral T H) τ' v ω := by
  filter_upwards [h.contIntegral_predInd_stopSet_all T H hτ, stoppedProcess_congr_ae (X := h.contIntegral T H) hττ]
    with ω h1 h2 v
  rw [h1, h2]

/-- **Stopping at a hitting time**: a raw stopping time `τ`, a.s. equal to `hitTime F Y`, gives
the stopped integral at the hitting time and the integrand `1{s ≤ hitTime F Y} H`. -/
theorem exists_stopped_integral_hitTime {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Y : ℝ≥0 → Ω → E} (hY : ∀ t, Measurable[𝓖 t] (Y t))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) {F : Set E} (hF : IsClosed F) :
    ∃ τ : Ω → WithTop ℝ≥0, ∃ hτ : IsStoppingTime 𝓖 τ,
      (∀ᵐ ω ∂Q, τ ω = Semimartingale.hitTime F Y ω) ∧
      (((predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H :
        PredL2 𝓖 (bracketMeasure Q α T)) : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ)
        =ᵐ[bracketMeasure Q α T] (stopSet (Semimartingale.hitTime F Y)).indicator
          ((H : Lp ℝ 2 (bracketMeasure Q α T)) : ℝ × Ω → ℝ) ∧
      ∀ᵐ ω ∂Q, ∀ v,
        h.contIntegral T (predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H) v ω =
          stoppedProcess (h.contIntegral T H) (Semimartingale.hitTime F Y) v ω := by
  obtain ⟨τ, hτ, -, hae⟩ := Semimartingale.exists_stoppingTime_ae_eq_hitTime hY hc hF
  exact ⟨τ, hτ, hae, predInd_stopSet_coeFn_ae (bracketMeasure_absolutelyContinuous Q α T) hτ
    hae H, h.contIntegral_predInd_stopSet_all_ae T H hτ hae⟩

end IsL2Integrator

/-!
### Cutoff extensions of coefficients
-/

variable {E : Type*} [TopologicalSpace E]

/-- **Cutoff**: `χ ∈ [0,1]` continuous, `1` on `W`, vanishing near `Uᶜ`, so `χ f` is continuous
for every `f` continuous on `U`. -/
theorem exists_cutoff [NormalSpace E] {U W : Set E} (hU : IsOpen U) (hW : IsClosed W)
    (hWU : W ⊆ U) :
    ∃ χ : E → ℝ, Continuous χ ∧ (∀ y, χ y ∈ Icc (0 : ℝ) 1) ∧ EqOn χ 1 W ∧
      (∀ y, y ∉ U → χ y = 0) ∧
      ∀ f : E → ℝ, ContinuousOn f U → Continuous fun y => χ y * f y := by
  obtain ⟨V, hVo, hWV, hVU⟩ := normal_exists_closure_subset hW hU hWU
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl hW
    (disjoint_compl_left_iff_subset.2 hWV)
  have hzero : ∀ y, y ∉ closure V → ∀ᶠ z in 𝓝 y, f z = 0 := fun y hy => by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    exact hf0 fun hzV => hz (subset_closure hzV)
  refine ⟨f, f.continuous, hf01, hf1, fun y hy => (hzero y fun h => hy (hVU h)).self_of_nhds,
    fun g hg => continuous_iff_continuousAt.2 fun y => ?_⟩
  by_cases hy : y ∈ U
  · exact f.continuous.continuousAt.mul (hg.continuousAt (hU.mem_nhds hy))
  · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 y] fun z => f z * g z := by
      filter_upwards [hzero y fun h => hy (hVU h)] with z hz
      rw [hz, zero_mul]
    exact continuousAt_const.congr hev

/-- **Continuous PSD extension** of a coefficient matrix continuous and PSD on `U`, agreeing with
it on the closed `W ⊆ U`. -/
theorem exists_continuous_psd_extension [NormalSpace E] {ι : Type*} [Fintype ι] {U W : Set E}
    (hU : IsOpen U) (hW : IsClosed W) (hWU : W ⊆ U) {φ : ι → ι → E → ℝ}
    (hφ : ∀ i j, ContinuousOn (φ i j) U)
    (hpsd : ∀ y ∈ U, ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * φ i j y) :
    ∃ ψ : ι → ι → E → ℝ, (∀ i j, Continuous (ψ i j)) ∧ (∀ i j, EqOn (ψ i j) (φ i j) W) ∧
      (∀ y (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * ψ i j y) ∧
      (∀ i j y, |ψ i j y| ≤ |φ i j y|) ∧
      (∀ i j y, φ i j y = φ j i y → ψ i j y = ψ j i y) := by
  obtain ⟨χ, -, hχ01, hχ1, hχ0, hχc⟩ := exists_cutoff hU hW hWU
  refine ⟨fun i j y => χ y * φ i j y, fun i j => hχc _ (hφ i j), fun i j y hy => ?_,
    fun y v => ?_, fun i j y => ?_, fun i j y hs => by simp only [hs]⟩
  · simp only [hχ1 hy, Pi.one_apply, one_mul]
  · have he : ∑ i, ∑ j, v i * v j * (χ y * φ i j y) = χ y * ∑ i, ∑ j, v i * v j * φ i j y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [he]
    by_cases hy : y ∈ U
    · exact mul_nonneg (hχ01 y).1 (hpsd y hy v)
    · rw [hχ0 y hy, zero_mul]
  · rw [abs_mul, abs_of_nonneg (hχ01 y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 y).2

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
