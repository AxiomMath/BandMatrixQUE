module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Optional
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Optional stopping for modifications: the main statement)

`exists_martingale_stoppedProcess`: on a probability space with a raw filtration `𝓖`, if `X`
has a.s. continuous paths and a `𝓖`-martingale modification, then for every `𝓖`-stopping time
`ρ` the stopped process `X^ρ` has a `𝓖`-martingale modification.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 m₀} {ρ : Ω → WithTop ℝ≥0}

theorem stoppedProcess_sub_integral {X M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 Q)
    (hMX : ∀ t, M t =ᵐ[Q] X t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hρ : IsStoppingTime 𝓖 ρ) {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun ω => stoppedProcess X ρ t ω - stoppedProcess X ρ s ω) Q ∧
    (∀ A, MeasurableSet[𝓖 s] A →
      ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω) ∂Q = 0) ∧
    ∀ᵐ ω ∂Q, Tendsto (fun n => gridTransform M ρ s t n ω) atTop
      (𝓝 (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω)) := by
  have hgood : ∀ᵐ ω ∂Q, ∀ n k, M (grid s t n k) ω = X (grid s t n k) ω := by
    simp only [ae_all_iff]; exact fun n k => hMX _
  have htr : ∀ᵐ ω ∂Q, Tendsto (fun n => gridTransform M ρ s t n ω) atTop
      (𝓝 (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω)) := by
    filter_upwards [hgood, hc] with ω h1 h2
    have := tendsto_telescope' h2 (ρ ω) hst
    refine this.congr fun n => ?_
    simp only [gridTransform, h1]
  set σ := fun n => gridStop ρ s t n
  have hσ : ∀ n, IsStoppingTime 𝓖 (σ n) := fun n => isStoppingTime_gridStop hρ hst n
  have hσle : ∀ n ω, σ n ω ≤ t := fun n ω => gridStop_le hst n ω
  set f : ℕ → Ω → ℝ := fun n => stoppedValue M (σ n)
  set g : Ω → ℝ := fun ω => stoppedProcess X ρ t ω - stoppedProcess X ρ s ω + M s ω
  have hf : ∀ n, f n = fun ω => gridTransform M ρ s t n ω + M s ω := fun n => by
    funext ω; simp only [f, σ, gridTransform_eq M hst n ω]; ring
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [htr] with ω h
    simp only [hf]; exact h.add_const _
  have hce : ∀ n, f n =ᵐ[Q] Q[M t | (hσ n).measurableSpace] := fun n =>
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσ n) (hσle n)
      (countable_range_gridStop s t n)
  have hUI : UniformIntegrable f 1 Q :=
    ((hM.integrable t).uniformIntegrable_condExp
      (fun n => (hσ n).measurableSpace_le_of_le (hσle n))).ae_eq fun n => (hce n).symm
  have hgi : Integrable g Q := hUI.integrable_of_ae_tendsto hlim
  have hfm : ∀ n, AEStronglyMeasurable (f n) Q := fun n =>
    (integrable_condExp.congr (hce n).symm).aestronglyMeasurable
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hfm
    (memLp_one_iff_integrable.2 hgi) hUI.1 hlim
  have hXi : Integrable (fun ω => stoppedProcess X ρ t ω - stoppedProcess X ρ s ω) Q := by
    have := hgi.sub (hM.integrable s)
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp [g]
  refine ⟨hXi, fun A hA => ?_, htr⟩
  set ι : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hAm : MeasurableSet A := 𝓖.le s A hA
  have hιm : AEStronglyMeasurable ι Q :=
    (stronglyMeasurable_const.indicator hAm).aestronglyMeasurable
  have hιb : ∀ᵐ ω ∂Q, ‖ι ω‖ ≤ 1 := ae_of_all _ fun ω => by
    by_cases h : ω ∈ A <;> simp [ι, h]
  have hFi : ∀ n, Integrable (fun ω => ι ω * f n ω) Q := fun n =>
    (integrable_condExp.congr (hce n).symm).bdd_mul hιm hιb
  have hFlim : Tendsto (fun n => ∫ ω, ι ω * f n ω ∂Q) atTop (𝓝 (∫ ω, ι ω * g ω ∂Q)) := by
    refine tendsto_integral_of_L1 _ (hgi.bdd_mul hιm hιb).aestronglyMeasurable
      (Eventually.of_forall hFi) ?_
    have hL1' : Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂Q) atTop (𝓝 0) := by
      refine hL1.congr fun n => ?_
      rw [eLpNorm_one_eq_lintegral_enorm ((hfm n).sub hgi.aestronglyMeasurable)]
      rfl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1'
      (fun n => zero_le) (fun n => ?_)
    refine lintegral_mono fun ω => ?_
    rw [← mul_sub, enorm_mul]
    calc ‖ι ω‖ₑ * ‖f n ω - g ω‖ₑ ≤ 1 * ‖f n ω - g ω‖ₑ := by
          gcongr
          by_cases h : ω ∈ A <;> simp [ι, h]
      _ = ‖f n ω - g ω‖ₑ := one_mul _
  have hFconst : ∀ n, ∫ ω, ι ω * f n ω ∂Q = ∫ ω, ι ω * M s ω ∂Q := fun n => by
    obtain ⟨hi1, hz⟩ := integral_indicator_gridTransform hM hρ hst hA n
    have hi2 : Integrable (fun ω => ι ω * M s ω) Q := (hM.integrable s).bdd_mul hιm hιb
    rw [hf n]
    simp only [mul_add]
    rw [integral_add hi1 hi2, hz, zero_add]
  have hlimeq : ∫ ω, ι ω * g ω ∂Q = ∫ ω, ι ω * M s ω ∂Q := by
    have := hFlim
    simp only [hFconst] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hi2 : Integrable (fun ω => ι ω * M s ω) Q := (hM.integrable s).bdd_mul hιm hιb
  have e : (fun ω => ι ω * (stoppedProcess X ρ t ω - stoppedProcess X ρ s ω)) =
      fun ω => ι ω * g ω - ι ω * M s ω := by
    funext ω; simp only [g]; ring
  rw [e, integral_sub (hgi.bdd_mul hιm hιb) hi2, hlimeq, sub_self]

/-- **Optional stopping for a.s. continuous processes with a martingale modification.** -/
theorem exists_martingale_stoppedProcess {X M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 Q)
    (hMX : ∀ t, M t =ᵐ[Q] X t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hρ : IsStoppingTime 𝓖 ρ) :
    ∃ M' : ℝ≥0 → Ω → ℝ, Martingale M' 𝓖 Q ∧ ∀ t, M' t =ᵐ[Q] stoppedProcess X ρ t := by
  have h0 : ∀ ω, stoppedProcess X ρ 0 ω = X 0 ω := fun ω => by
    rw [stoppedProcess_eq_stopTime, le_antisymm (stopTime_le _ 0) zero_le]
  have hint : ∀ t, Integrable (stoppedProcess X ρ t) Q := fun t => by
    obtain ⟨h1, -, -⟩ := stoppedProcess_sub_integral hM hMX hc hρ (zero_le : (0 : ℝ≥0) ≤ t)
    have := h1.add (hM.integrable 0)
    refine this.congr ?_
    filter_upwards [hMX 0] with ω hω
    simp [h0, hω]
  have hmeas : ∀ t, AEStronglyMeasurable[𝓖 t] (stoppedProcess X ρ t) Q := fun t => by
    obtain ⟨-, -, h3⟩ := stoppedProcess_sub_integral hM hMX hc hρ (zero_le : (0 : ℝ≥0) ≤ t)
    have hsm : ∀ n, StronglyMeasurable[𝓖 t] (fun ω => gridTransform M ρ 0 t n ω + M 0 ω) := by
      intro n
      refine (Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_).add
        ((hM.1 0).mono (𝓖.mono zero_le))
      have hk := Finset.mem_range.1 hk
      have h0t : (0 : ℝ≥0) ≤ t := zero_le
      have l0 := 𝓖.mono (show grid 0 t n k ≤ t by
        have := grid_mono h0t n hk.le; rwa [grid_last h0t] at this)
      have l1 := 𝓖.mono (show grid 0 t n (k + 1) ≤ t by
        have := grid_mono h0t n (Nat.succ_le_of_lt hk); rwa [grid_last h0t] at this)
      have hB : MeasurableSet[𝓖 t] {ω | (grid 0 t n k : WithTop ℝ≥0) < ρ ω} := by
        have := l0 _ (hρ (grid 0 t n k)).compl
        convert this using 1; ext ω; simp only [mem_ofPred, mem_compl_iff]; exact not_le.symm
      classical
      have e : (fun ω => if (grid 0 t n k : WithTop ℝ≥0) < ρ ω then
          M (grid 0 t n (k + 1)) ω - M (grid 0 t n k) ω else 0) =
          {ω | (grid 0 t n k : WithTop ℝ≥0) < ρ ω}.indicator
            (fun ω => M (grid 0 t n (k + 1)) ω - M (grid 0 t n k) ω) := by
        funext ω
        by_cases h : (grid 0 t n k : WithTop ℝ≥0) < ρ ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | (grid 0 t n k : WithTop ℝ≥0) < ρ ω} from h)]
          split_ifs; rfl
        · rw [Set.indicator_of_notMem
            (show ω ∉ {ω | (grid 0 t n k : WithTop ℝ≥0) < ρ ω} from h)]
          split_ifs; rfl
      rw [e]
      exact ((((hM.1 _).mono l1).sub ((hM.1 _).mono l0))).indicator hB
    refine aestronglyMeasurable_of_tendsto_ae_sub (fun n => (hsm n).aestronglyMeasurable) ?_
    filter_upwards [h3, hMX 0] with ω hω hω0
    have := hω.add_const (M 0 ω)
    rwa [h0, ← hω0, sub_add_cancel] at this
  refine exists_martingale_modification hint hmeas fun s t hst A hA => ?_
  obtain ⟨h1, h2, -⟩ := stoppedProcess_sub_integral hM hMX hc hρ hst
  have := h2 A hA
  have hAm : MeasurableSet A := 𝓖.le s A hA
  rw [← integral_indicator hAm, ← integral_indicator hAm, ← sub_eq_zero,
    ← integral_sub ((hint t).indicator hAm) ((hint s).indicator hAm)]
  rw [← this]
  congr 1; funext ω
  by_cases h : ω ∈ A <;> simp [h]

end BlockBand.SourceProcess.Stochastic.Semimartingale
