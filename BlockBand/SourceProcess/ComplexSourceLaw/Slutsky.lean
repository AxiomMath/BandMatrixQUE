module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Slutsky's lemma on varying probability spaces

Mathlib's
`tendstoInDistribution_of_tendstoInMeasure_sub` needs one probability space for all indices; the
source data at width `W_j` live on `probedPathLaw W_j`, so we prove the varying-space version
(same three-piece estimate, bounded Lipschitz tests, then the portmanteau equivalence).

`tendsto_integral_of_close`: if `∫Φ(Y_j)dμ_j → ∫Φdν` for every bounded continuous `Φ` and
`μ_j{‖X_j - Y_j‖ ≥ ε} → 0` for every `ε > 0`, then `∫Φ(X_j)dμ_j → ∫Φdν` for every bounded
continuous `Φ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)] {μ : ∀ j, Measure (Ω j)}
  [∀ j, IsProbabilityMeasure (μ j)] {X Y : ∀ j, Ω j → E}

/-- The pointwise three-piece bound, integrated: for an `L`-Lipschitz `F` with oscillation
`≤ C`, `|∫F(X) - ∫F(Y)| ≤ Lδ + C μ{δ ≤ ‖X - Y‖}`. -/
theorem abs_integral_sub_le {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {U V : α → E} (hU : Measurable U) (hV : Measurable V)
    {F : E → ℝ} {C : ℝ} (hC : ∀ x y, dist (F x) (F y) ≤ C) {L : ℝ≥0} (hL : LipschitzWith L F)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    |∫ a, F (U a) ∂ρ - ∫ a, F (V a) ∂ρ| ≤ L * δ + C * ρ.real {a | δ ≤ ‖U a - V a‖} := by
  have hFc : Continuous F := hL.continuous
  have hbd : ∀ x, ‖F x‖ ≤ ‖F 0‖ + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (F x) (F 0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]; linarith
  have hIU : Integrable (fun a => F (U a)) ρ :=
    Integrable.of_bound (hFc.measurable.comp hU).aestronglyMeasurable (‖F 0‖ + C)
      (ae_of_all _ fun a => hbd _)
  have hIV : Integrable (fun a => F (V a)) ρ :=
    Integrable.of_bound (hFc.measurable.comp hV).aestronglyMeasurable (‖F 0‖ + C)
      (ae_of_all _ fun a => hbd _)
  set S : Set α := {a | δ ≤ ‖U a - V a‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const (hU.sub hV).norm
  have hpt : ∀ a, |F (U a) - F (V a)| ≤ L * δ + S.indicator (fun _ => C) a := by
    intro a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]
      have := hC (U a) (V a)
      rw [Real.dist_eq] at this
      have : (0 : ℝ) ≤ L * δ := mul_nonneg L.2 hδ
      linarith
    · rw [Set.indicator_of_notMem ha]
      have hlt : ‖U a - V a‖ < δ := lt_of_not_ge ha
      have := hL.dist_le_mul (U a) (V a)
      rw [Real.dist_eq, dist_eq_norm] at this
      have : (L : ℝ) * ‖U a - V a‖ ≤ L * δ := mul_le_mul_of_nonneg_left hlt.le L.2
      linarith
  rw [← integral_sub hIU hIV]
  calc |∫ a, F (U a) - F (V a) ∂ρ| ≤ ∫ a, |F (U a) - F (V a)| ∂ρ := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans_eq (by simp [Real.norm_eq_abs])
    _ ≤ ∫ a, (L * δ + S.indicator (fun _ => C) a) ∂ρ := by
        refine integral_mono (hIU.sub hIV).abs ?_ hpt
        exact (integrable_const _).add ((integrable_const C).indicator hS)
    _ = L * δ + C * ρ.real S := by
        rw [integral_add (integrable_const _) ((integrable_const C).indicator hS),
          integral_const, integral_indicator_const C hS]
        simp [mul_comm]

/-- **Slutsky on varying spaces.** -/
theorem tendsto_integral_of_close (hX : ∀ j, Measurable (X j)) (hY : ∀ j, Measurable (Y j))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hYν : ∀ Φ : E →ᵇ ℝ, Tendsto (fun j => ∫ ω, Φ (Y j ω) ∂μ j) atTop (𝓝 (∫ y, Φ y ∂ν)))
    (hXY : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => μ j {ω | ε ≤ ‖X j ω - Y j ω‖}) atTop (𝓝 0)) :
    ∀ Φ : E →ᵇ ℝ, Tendsto (fun j => ∫ ω, Φ (X j ω) ∂μ j) atTop (𝓝 (∫ y, Φ y ∂ν)) := by
  let lX : ℕ → ProbabilityMeasure E := fun j => ⟨(μ j).map (X j), inferInstance⟩
  let lν : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmap : ∀ (F : E → ℝ), Continuous F → ∀ j,
      ∫ x, F x ∂((lX j : Measure E)) = ∫ ω, F (X j ω) ∂μ j := fun F hF j =>
    integral_map (hX j).aemeasurable hF.aestronglyMeasurable
  have hlim : Tendsto lX atTop (𝓝 lν) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro F ⟨C, hC⟩ ⟨L, hL⟩
    have hFc : Continuous F := hL.continuous
    let Φ : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, hFc⟩ C hC
    have hYF := hYν Φ
    simp only [hmap F hFc]
    show Tendsto (fun j => ∫ ω, F (X j ω) ∂μ j) atTop (𝓝 (∫ y, F y ∂ν))
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ : ℝ := ε / (4 * (L + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hC0 : 0 ≤ C := (dist_nonneg).trans (hC 0 0)
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hYF (ε / 2) (by positivity)
    have hP : Tendsto (fun j => (μ j).real {ω | δ ≤ ‖X j ω - Y j ω‖}) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hXY δ hδ)
      simpa [Function.comp_def, measureReal_def] using this
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hP (ε / (4 * (C + 1))) (by positivity)
    refine ⟨max N₁ N₂, fun j hj => ?_⟩
    have h1 := hN₁ j (le_of_max_le_left hj)
    have h2 := hN₂ j (le_of_max_le_right hj)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h2
    have h3 := abs_integral_sub_le (μ j) (hX j) (hY j) hC hL hδ.le
    have hYeq : ∫ ω, Φ (Y j ω) ∂μ j = ∫ ω, F (Y j ω) ∂μ j := rfl
    have hνeq : ∫ y, Φ y ∂ν = ∫ y, F y ∂ν := rfl
    rw [hYeq, hνeq, Real.dist_eq] at h1
    rw [Real.dist_eq]
    have hLδ : (L : ℝ) * δ ≤ ε / 4 := by
      rw [show (L : ℝ) * δ = ε / 4 * (L / (L + 1)) by simp only [δ]; field_simp]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    have hCP : C * (μ j).real {ω | δ ≤ ‖X j ω - Y j ω‖} ≤ ε / 4 := by
      calc C * (μ j).real {ω | δ ≤ ‖X j ω - Y j ω‖} ≤ C * (ε / (4 * (C + 1))) :=
            mul_le_mul_of_nonneg_left h2.le hC0
        _ = ε / 4 * (C / (C + 1)) := by field_simp
        _ ≤ ε / 4 := mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).2 (by linarith))
    calc |∫ ω, F (X j ω) ∂μ j - ∫ y, F y ∂ν|
        ≤ |∫ ω, F (X j ω) ∂μ j - ∫ ω, F (Y j ω) ∂μ j| +
            |∫ ω, F (Y j ω) ∂μ j - ∫ y, F y ∂ν| := abs_sub_le _ _ _
      _ < ε := by linarith
  intro Φ
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) Φ
  simp only [hmap Φ Φ.continuous] at this
  exact this

end BlockBand.SourceProcess.ComplexSourceLaw
