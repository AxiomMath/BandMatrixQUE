module
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Nonnegative continuous semimartingales with nonpositive drift

On an arbitrary filtered probability space `(Ω, Q, 𝓖)` (contract `IsContinuousSemimartingale`,
no usual conditions):

`lintegral_le_of_nonpos_drift`: if a real continuous semimartingale `Z` (in `ℝ¹`) is a.s.
nonnegative at all times and its drift is a.s. `≤ 0` at all times, then for every `𝓖_0`-event
`A` on which `Z_0` is bounded,
`∫_A Z_t dQ ≤ ∫_A Z_0 dQ` (as lower Lebesgue integrals of `ofReal`).

Proof. Along the localizing sequence `τ_k`, `Z_{t∧τ_k} ≤ Z_0 + N_t` pathwise, with `N` the stopped
compensated process (the drift integral is `≤ 0`); `N` has a martingale modification `M` with
`M_0 = N_0 = 0`, so `∫_A N_t = ∫_A M_t = ∫_A M_0 = 0` (`A ∈ 𝓖_0`). Then Fatou in `k`
(`τ_k → ⊤` a.s., so `Z_{t∧τ_k} = Z_t` eventually). No integrability of `Z_t` is assumed.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Nonnegative semimartingales with nonpositive drift decrease in mean on `𝓖_0`-events.** -/
theorem lintegral_le_of_nonpos_drift {Z β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (h : IsContinuousSemimartingale Q 𝓖 Z β α)
    (hβ : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0, β s ω 0 ≤ 0) (hZ : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω 0)
    {A : Set Ω} (hA : MeasurableSet[𝓖 0] A) {B : ℝ} (hB : ∀ ω ∈ A, Z 0 ω 0 ≤ B) (t : ℝ≥0) :
    ∫⁻ ω in A, ENNReal.ofReal (Z t ω 0) ∂Q ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω 0) ∂Q := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := h.localizing
  have hAm : MeasurableSet A := 𝓖.le 0 _ hA
  have hZ0m : StronglyMeasurable fun ω => Z 0 ω 0 :=
    (continuous_apply 0).comp_stronglyMeasurable ((h.adapted 0).mono (𝓖.le 0))
  have hZ0int : IntegrableOn (fun ω => Z 0 ω 0) A Q := by
    refine Measure.integrableOn_of_bounded (measure_ne_top _ _) hZ0m.aestronglyMeasurable
      (M := max B 0) ?_
    refine (ae_restrict_iff' hAm).2 ?_
    filter_upwards [hZ] with ω hω hωA
    rw [Real.norm_eq_abs, abs_of_nonneg (hω 0)]
    exact (hB ω hωA).trans (le_max_left _ _)
  have hk : ∀ k, ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω 0) ∂Q ≤
      ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω 0) ∂Q := by
    intro k
    obtain ⟨M, hM, hMe⟩ := (hmart k).1 0
    set N := stoppedProcess (smCompensated Z β 0) (τ k) with hNdef
    have hN0 : ∀ ω, N 0 ω = 0 := fun ω => by
      have h0 : (min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ k ω)).untopA = 0 := by
        rw [min_eq_left (by rw [WithTop.coe_zero]; exact zero_le)]
        rfl
      simp only [N, stoppedProcess, smCompensated, h0, sub_self, NNReal.coe_zero,
        Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    have hNint : Integrable (N t) Q := (hM.integrable t).congr (hMe t)
    have hint0 : ∫ ω in A, N t ω ∂Q = 0 := by
      rw [← integral_congr_ae (ae_restrict_of_ae (hMe t)), ← hM.setIntegral_eq zero_le hA,
        integral_congr_ae (ae_restrict_of_ae (hMe 0))]
      simp [hN0]
    have hpt : ∀ᵐ ω ∂Q, stoppedProcess Z (τ k) t ω 0 ≤ Z 0 ω 0 + N t ω := by
      filter_upwards [hβ] with ω hω
      simp only [N, stoppedProcess, smCompensated]
      have : ∫ s in Ioc (0 : ℝ) ((min (t : WithTop ℝ≥0) (τ k ω)).untopA : ℝ),
          β s.toNNReal ω 0 ≤ 0 := setIntegral_nonpos measurableSet_Ioc fun s _ => hω _
      linarith
    have hnn : ∀ᵐ ω ∂Q, 0 ≤ Z 0 ω 0 + N t ω := by
      filter_upwards [hpt, hZ] with ω h1 h2
      exact (h2 _).trans h1
    calc ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω 0) ∂Q
        ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω 0 + N t ω) ∂Q :=
          lintegral_mono_ae (ae_restrict_of_ae (hpt.mono fun ω h => ENNReal.ofReal_le_ofReal h))
      _ = ENNReal.ofReal (∫ ω in A, (Z 0 ω 0 + N t ω) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal (hZ0int.add hNint.integrableOn)
            (ae_restrict_of_ae hnn)).symm
      _ = ENNReal.ofReal (∫ ω in A, Z 0 ω 0 ∂Q) := by
          rw [integral_add hZ0int hNint.integrableOn, hint0, add_zero]
      _ = ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω 0) ∂Q :=
          ofReal_integral_eq_lintegral_ofReal hZ0int (ae_restrict_of_ae (hZ.mono fun ω h => h 0))
  have hmeas : ∀ k, Measurable fun ω => ENNReal.ofReal (stoppedProcess Z (τ k) t ω 0) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_apply 0).comp_stronglyMeasurable
      ((h.progressive.stronglyAdapted_stoppedProcess (hτ k) t).mono (𝓖.le t))).measurable
  calc ∫⁻ ω in A, ENNReal.ofReal (Z t ω 0) ∂Q
      = ∫⁻ ω in A, liminf (fun k => ENNReal.ofReal (stoppedProcess Z (τ k) t ω 0)) atTop ∂Q := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hτlim] with ω hω
        refine (Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)).symm
        filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hω t] with k hk
        rw [stoppedProcess_eq_of_le hk.le]
    _ ≤ liminf (fun k => ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω 0) ∂Q) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω 0) ∂Q :=
        liminf_le_of_frequently_le' (Frequently.of_forall hk)

end BlockBand.SourceProcess.Stochastic.NativeSDE
