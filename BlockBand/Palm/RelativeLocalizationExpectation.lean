module

public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Relative localization: nonpositive drift decreases the mean

For a bounded real continuous semimartingale with nonpositive drift, `E Y_t ≤ E Y_0`
(`integral_le_of_drift_nonpos`), by localization and dominated convergence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Filter Topology BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-- **Nonpositive drift decreases the mean** (bounded real continuous semimartingale). -/
theorem integral_le_of_drift_nonpos {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (Y : ℝ≥0 → Ω → Fin 1 → ℝ) (β : ℝ≥0 → Ω → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ) (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    {C : ℝ} (hC : ∀ t ω, |Y t ω 0| ≤ C)
    (hβ : ∀ᵐ ω ∂Q, ∀ r : ℝ≥0, ∫ s in Set.Ioc (0 : ℝ) r, β s.toNNReal ω 0 ≤ 0) (t : ℝ≥0) :
    ∫ ω, Y t ω 0 ∂Q ≤ ∫ ω, Y 0 ω 0 ∂Q := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := hY.localizing
  have hmeasY : ∀ s, Measurable fun ω => Y s ω 0 := fun s =>
    (continuous_apply 0).measurable.comp ((hY.adapted s).mono (𝓖.le s)).measurable
  -- the stopped values
  set g : ℕ → Ω → ℝ := fun n ω => stoppedProcess Y (τ n) t ω 0 - Y 0 ω 0 with hg
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) Q := by
    intro n
    have h1 := hY.progressive.stronglyMeasurable_stoppedProcess (hτ n) t
    exact (((continuous_apply 0).measurable.comp h1.measurable).sub (hmeasY 0)).aestronglyMeasurable
  have hgbd : ∀ n, ∀ ω, ‖g n ω‖ ≤ 2 * C := by
    intro n ω
    have h1 := hC ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) ω
    have h2 := hC 0 ω
    rw [Real.norm_eq_abs]
    simp only [hg, stoppedProcess]
    calc _ ≤ |Y ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) ω 0| + |Y 0 ω 0| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  -- each stopped mean is nonpositive
  have hstep : ∀ n, ∫ ω, g n ω ∂Q ≤ 0 := by
    intro n
    obtain ⟨M, hM, hMeq⟩ := (hmart n).1 0
    have hint : ∫ ω, M t ω ∂Q = ∫ ω, M 0 ω ∂Q := by
      have := hM.setIntegral_eq (zero_le (a := t)) (MeasurableSet.univ (m := 𝓖 0))
      simpa only [Measure.restrict_univ] using this.symm
    have hM0 : M 0 =ᵐ[Q] fun _ => 0 := by
      filter_upwards [hMeq 0] with ω hω
      rw [hω]
      simp [stoppedProcess, smCompensated]
    have hint0 : ∫ ω, M t ω ∂Q = 0 := by rw [hint, integral_congr_ae hM0, integral_zero]
    have hle : ∀ᵐ ω ∂Q, g n ω ≤ M t ω := by
      filter_upwards [hMeq t, hβ] with ω hω hβω
      rw [hω]
      simp only [hg, stoppedProcess, smCompensated]
      have := hβω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA)
      linarith
    have hgint : Integrable (g n) Q :=
      Integrable.of_bound (hgmeas n) (2 * C) (Eventually.of_forall (hgbd n))
    calc ∫ ω, g n ω ∂Q ≤ ∫ ω, M t ω ∂Q := integral_mono_ae hgint (hM.integrable t) hle
      _ = 0 := hint0
  -- pass to the limit
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => g n ω) atTop (𝓝 (Y t ω 0 - Y 0 ω 0)) := by
    filter_upwards [hτlim] with ω hω
    have hev : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hg, stoppedProcess, min_eq_left hn.le]; rfl
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => 2 * C) hgmeas
    (integrable_const _) (fun n => Eventually.of_forall (hgbd n)) hlim
  have hle0 : ∫ ω, (Y t ω 0 - Y 0 ω 0) ∂Q ≤ 0 :=
    le_of_tendsto hconv (Eventually.of_forall hstep)
  have hi : ∀ s, Integrable (fun ω => Y s ω 0) Q := fun s =>
    Integrable.of_bound (hmeasY s).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC s ω)
  rw [integral_sub (hi t) (hi 0)] at hle0
  linarith

end BlockBand.Palm.RelativeLocalization
