module

public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionSuper

/-!
# Nonnegative semimartingales with nonpositive drift at positive times

A variant of `lintegral_le_of_nonpos_drift` with the drift hypothesis required only at times
`s > 0`. The original proof uses the drift only through `∫_{(0,t]} β`, so the argument is
unchanged. This form is needed when the drift at `s = 0` is not controlled (a process killed at
time `0` off a `𝓖₀`-event keeps its time-`0` characteristics).

Setting: any filtered probability space `(Ω, Q, 𝓖)` and an `IsContinuousSemimartingale`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Supermartingale bound with the drift controlled at positive times only.** -/
theorem lintegral_le_of_nonpos_drift_pos {Z β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (h : IsContinuousSemimartingale Q 𝓖 Z β α)
    (hβ : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0, 0 < s → β s ω 0 ≤ 0) (hZ : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω 0)
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
          β s.toNNReal ω 0 ≤ 0 :=
        setIntegral_nonpos measurableSet_Ioc fun s hs => hω _ (Real.toNNReal_pos.2 hs.1)
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

end BlockBand.Transmission.DualFeller
