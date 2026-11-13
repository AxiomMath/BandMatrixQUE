module

public import BlockBand.SourceProcess.RankFree.LocMart
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularOS
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Elementary

/-!
# Increments after a stopping time with an `𝓕_τ`-measurable weight

* `stronglyMeasurable_ite_le`: an `𝓕_τ`-measurable `f` switched on at `{τ ≤ t}` is
  `𝓖_t`-measurable.
* `hmm_mul_sub_stopped`: if `Φ` has a martingale modification and a.s. continuous paths, `ζ` is
  bounded and `𝓕_τ`-measurable, then `ζ (Φ_t - Φ_{t∧τ})` has a martingale modification
  (optional sampling at `τ ∨ s`, `integral_mul_sub_stopped_eq_zero`).
* `LocMart.shift`: `ζ (Z_t - Z_{t∧τ})` is a `LocMart` with drift `1{τ < s} ζ β_s`.

This is the "shared birth" step of: a vector chosen at the stopping time `τ`
pairs with the increments of the frame after `τ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Dyson.Angular (integral_mul_sub_stopped_eq_zero
  integrable_sub_stopped)
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] in
/-- An `𝓕_τ`-measurable function switched on at `{τ ≤ t}` is `𝓖_t`-measurable. -/
theorem stronglyMeasurable_ite_le {m₀ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m₀}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) {E : Type*} [TopologicalSpace E] [Zero E]
    {f : Ω → E} (hf : StronglyMeasurable[hτ.measurableSpace] f) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (fun ω => if τ ω ≤ t then f ω else 0) := by
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on (m := hτ.measurableSpace)
    (s := {ω | τ ω ≤ t}) (hτ.measurableSet_le' t) (fun A hA => ?_) ?_ fun x hx => ite_eq_right hx
  · have h := ((hτ.measurableSet _).1 hA).2 t
    rwa [inter_right_comm, inter_self] at h
  · exact StronglyMeasurable.ite (hτ.measurableSet_le' t) hf stronglyMeasurable_const

/-- Martingale modifications transfer along a.s. equal paths. -/
theorem hmm_congr' {F G : ℝ≥0 → Ω → ℝ} (h : HasMartingaleModification Q 𝓖 G)
    (hFG : ∀ᵐ ω ∂Q, ∀ t, F t ω = G t ω) : HasMartingaleModification Q 𝓖 F := by
  obtain ⟨M, hM, hMG⟩ := h
  refine ⟨M, hM, fun t => ?_⟩
  filter_upwards [hMG t, hFG] with ω h1 h2
  rw [h1, h2]

variable [IsProbabilityMeasure Q]

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem sub_stopped_sub {Φ : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t)
    (ω : Ω) :
    (Φ t ω - stoppedProcess Φ τ t ω) - (Φ s ω - stoppedProcess Φ τ s ω) =
      Φ t ω - stoppedProcess Φ (fun ω => max (τ ω) (s : WithTop ℝ≥0)) t ω := by
  rcases le_or_gt (τ ω) s with h | h
  · have e : stoppedProcess Φ (fun ω => max (τ ω) (s : WithTop ℝ≥0)) t ω = Φ s ω := by
      rw [stoppedProcess_eq_of_ge (by rw [max_eq_right h]; exact WithTop.coe_le_coe.2 hst),
        max_eq_right h]
      rfl
    rw [stoppedProcess_eq_of_ge (h.trans (WithTop.coe_le_coe.2 hst)), stoppedProcess_eq_of_ge h, e]
    ring
  · rw [stoppedProcess_eq_of_le h.le, sub_self, sub_zero, stoppedProcess, stoppedProcess,
      max_eq_left h.le]

/-- **Optional sampling after `τ`.** -/
theorem hmm_mul_sub_stopped {Φ : ℝ≥0 → Ω → ℝ} (hΦ : HasMartingaleModification Q 𝓖 Φ)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Φ t ω) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    {ζ : Ω → ℝ} (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) {C : ℝ}
    (hζb : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    HasMartingaleModification Q 𝓖 (fun t ω => ζ ω * (Φ t ω - stoppedProcess Φ τ t ω)) := by
  set K : ℝ≥0 → Ω → ℝ := fun t ω => ζ ω * (Φ t ω - stoppedProcess Φ τ t ω) with hK
  have hζm : StronglyMeasurable ζ := hζ.mono hτ.measurableSpace_le
  have hint : ∀ t, Integrable (K t) Q := fun t =>
    (integrable_sub_stopped hΦ hc hτ t).bdd_mul hζm.aestronglyMeasurable hζb
  obtain ⟨M, hM, hMΦ⟩ := hΦ
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMΦ hc hτ
  have hmeas : ∀ t, AEStronglyMeasurable[𝓖 t] (K t) Q := fun t => by
    refine ((stronglyMeasurable_ite_le hτ hζ t).mul ((hM.1 t).sub (hM'.1 t))).aestronglyMeasurable
      |>.congr ?_
    filter_upwards [hMΦ t, hM'X t] with ω h1 h2
    simp only [hK, Pi.mul_apply, Pi.sub_apply, h1, h2]
    split_ifs with h
    · rfl
    · rw [stoppedProcess_eq_of_le (not_le.1 h).le]; ring
  have hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓖 s] A →
      ∫ ω in A, K t ω ∂Q = ∫ ω in A, K s ω ∂Q := by
    intro s t hst A hA
    have hAm : MeasurableSet A := 𝓖.le s _ hA
    set ρ : Ω → WithTop ℝ≥0 := fun ω => max (τ ω) (s : WithTop ℝ≥0)
    have hρ : IsStoppingTime 𝓖 ρ := hτ.max_const s
    have hζA : StronglyMeasurable[hρ.measurableSpace] (A.indicator ζ) :=
      (hζ.mono (hτ.measurableSpace_mono hρ fun ω => le_max_left _ _)).indicator
        (hρ.le_measurableSpace_of_const_le (fun ω => le_max_right _ _) _ hA)
    have hb : ∀ᵐ ω ∂Q, ‖A.indicator ζ ω‖ ≤ C := by
      filter_upwards [hζb] with ω h
      by_cases hω : ω ∈ A
      · rwa [indicator_of_mem hω]
      · rw [indicator_of_notMem hω, norm_zero]; exact (norm_nonneg _).trans h
    have h0 := integral_mul_sub_stopped_eq_zero ⟨M, hM, hMΦ⟩ hc hρ hζA hb t
    rw [← sub_eq_zero, ← integral_sub (hint t).integrableOn (hint s).integrableOn,
      ← integral_indicator hAm, ← h0]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, hK, ← mul_sub, sub_stopped_sub hst, ρ]
    · simp [indicator_of_notMem hω]
  refine ⟨fun t => Q[K t | 𝓖 t], ?_, fun t => condExp_of_aestronglyMeasurable' (𝓖.le t)
    (hmeas t) (hint t)⟩
  refine BlockBand.SourceProcess.Stochastic.GeneralIntegral.martingale_of_setIntegral (fun t => stronglyMeasurable_condExp)
    (fun t => integrable_condExp) fun u v huv B hB => ?_
  rw [setIntegral_condExp (𝓖.le v) (hint v) (𝓖.mono huv B hB),
    setIntegral_condExp (𝓖.le u) (hint u) hB, hset u v huv B hB]

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem setIntegral_ite_lt {f : ℝ → ℝ} (r : WithTop ℝ≥0) (u : ℝ≥0)
    (hf : IntegrableOn f (Ioc 0 u)) :
    ∫ v in Ioc (0 : ℝ) u, (if r < (v.toNNReal : WithTop ℝ≥0) then f v else 0) =
      (∫ v in Ioc (0 : ℝ) u, f v) - ∫ v in Ioc (0 : ℝ) (stopTime r u), f v := by
  have e : (fun v : ℝ => if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0) =
      {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r}.indicator f := by
    funext v; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hg : IntegrableOn (fun v : ℝ => if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0)
      (Ioc 0 u) := by
    rw [e]
    exact hf.indicator (measurableSet_toNNReal_le r)
  calc ∫ v in Ioc (0 : ℝ) u, (if r < (v.toNNReal : WithTop ℝ≥0) then f v else 0)
      = ∫ v in Ioc (0 : ℝ) u, (f v - if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0) := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        dsimp only
        split_ifs with h1 h2 h2
        · exact absurd h2 (not_le.2 h1)
        · ring
        · ring
        · exact absurd (not_lt.1 h1) h2
    _ = _ := by rw [integral_sub hf hg, setIntegral_switch f r u]

variable {Z β : ℝ≥0 → Ω → ℝ}

/-- **Increments after `τ` with an `𝓕_τ`-measurable bounded weight.** -/
theorem LocMart.shift (h : LocMart Q 𝓖 Z β) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    {ζ : Ω → ℝ} (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) {C : ℝ}
    (hζb : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    LocMart Q 𝓖 (fun t ω => ζ ω * (Z t ω - stoppedProcess Z τ t ω))
      (fun s ω => if τ ω < (s : WithTop ℝ≥0) then ζ ω * β s ω else 0) := by
  obtain ⟨σ, hσ, hl, hm⟩ := h.loc
  refine ⟨fun i => ?_, ?_, ?_, σ, hσ, hl, fun n => ?_⟩
  · convert ((stronglyMeasurable_ite_le hτ hζ i).comp_measurable measurable_snd).mul
      ((h.prog i).sub ((h.prog.stoppedProcess hτ) i)) using 1
    funext p
    simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
    split_ifs with hp
    · rfl
    · have hle : ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 :=
        (WithTop.coe_le_coe.2 (mem_Iic.1 p.1.2)).trans (not_le.1 hp).le
      rw [stoppedProcess_eq_of_le hle]
      ring
  · filter_upwards [h.cont] with ω hω
    exact continuous_const.mul (hω.sub (hω.comp (continuous_stopTime (τ ω))))
  · filter_upwards [h.integ] with ω hω t
    have e : (fun s : ℝ => if τ ω < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) then
        ζ ω * β s.toNNReal ω else 0) = {s : ℝ | τ ω < (s.toNNReal : WithTop ℝ≥0)}.indicator
          (fun s => ζ ω * β s.toNNReal ω) := by
      funext s; simp only [indicator_apply, mem_ofPred_eq]
    rw [e]
    exact ((hω t).const_mul (ζ ω)).indicator
      (measurableSet_lt measurable_const (WithTop.measurable_coe.comp measurable_real_toNNReal))
  · have hΦc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (locComp Z β) (σ n) t ω := by
      filter_upwards [h.cont_comp] with ω hω
      exact hω.comp (continuous_stopTime _)
    refine hmm_congr' (hmm_mul_sub_stopped (hm n) hΦc hτ hζ hζb) ?_
    filter_upwards [h.integ] with ω hω t
    have h0 : stopTime (τ ω) 0 = 0 := le_antisymm (stopTime_le _ 0) zero_le
    simp only [stoppedProcess_eq_stopTime, locComp]
    rw [stopTime_comm (σ n ω) (τ ω) t, h0,
      setIntegral_ite_lt (τ ω) _ ((hω _).const_mul (ζ ω)), integral_const_mul, integral_const_mul]
    ring

end BlockBand.SourceProcess.RankFree
