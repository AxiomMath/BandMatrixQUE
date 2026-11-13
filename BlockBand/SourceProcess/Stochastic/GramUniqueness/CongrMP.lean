module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Exhaust
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Congruence of martingale problems on the set where a solution lives

* `ae_ae_mem_of_forall`: if `Y_t ∈ F` a.s. for every `t` (`F` measurable, paths a.s.
  continuous), then a.s. `Y_r ∈ F` for Lebesgue-a.e. `r` (Fubini through the jointly
  measurable `jointVersion`).
* **`isMPSolutionOn_congr_on`**: let `Y` solve the `(b, a)` martingale problem in `U`, let
  `W ⊆ U` be open and `a, a'` continuous. If `Y_t ∈ F` a.s. for every `t` and `a = a'` on
  `F ∩ W`, then `Y` solves the `(b, a')` martingale problem in `W`. (The bracket compensators
  only see `Y_r` for `r` below the exit time from an interior domain of `W`, where `Y_r ∈ W`.)
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem ae_ae_mem_of_forall {Q : Measure Ω} [SFinite Q] {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hYm : ∀ t, Measurable (Y t)) (hc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {F : Set (Fin d → ℝ)} (hFm : MeasurableSet F) (hF : ∀ t, ∀ᵐ ω ∂Q, Y t ω ∈ F) :
    ∀ᵐ ω ∂Q, ∀ᵐ r ∂(volume : Measure ℝ), Y r.toNNReal ω ∈ F := by
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set hc
  have hJ : Measurable (jointVersion Y A) := measurable_jointVersion hYm hA hAc
  set E : Set (ℝ × Ω) := {p | jointVersion Y A p ∉ F}
  have hE : MeasurableSet E := (hJ hFm).compl
  have hA' : ∀ᵐ ω ∂Q, ω ∈ A := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω h
    simpa using h
  have h1 : (volume.prod Q) E = 0 := by
    rw [Measure.measure_prod_null hE]
    refine Eventually.of_forall fun r => ?_
    show Q {ω | ¬ jointVersion Y A (r, ω) ∈ F} = 0
    have : ∀ᵐ ω ∂Q, jointVersion Y A (r, ω) ∈ F := by
      filter_upwards [hA', hF r.toNNReal] with ω hω hY
      rw [jointVersion_of_mem hω]; exact hY
    exact ae_iff.1 this
  have h2 : (Q.prod volume) (Prod.swap ⁻¹' E) = 0 := by
    rw [← Measure.map_apply measurable_swap hE, Measure.prod_swap]; exact h1
  rw [Measure.measure_prod_null (measurable_swap hE)] at h2
  filter_upwards [h2, hA'] with ω hω hωA
  rw [ae_iff]
  have e : {r : ℝ | ¬ Y r.toNNReal ω ∈ F} = Prod.mk ω ⁻¹' (Prod.swap ⁻¹' E) := by
    ext r
    simp [E, jointVersion_of_mem hωA]
  rw [e]
  exact hω

/-- **Congruence on the set where the solution lives.** -/
theorem isMPSolutionOn_congr_on {Q : Measure Ω} [SFinite Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a a' : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U W : Set (Fin d → ℝ)}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : IsMPSolutionOn Q 𝓖 b a U Y) (hWU : W ⊆ U) (hW : IsOpen W)
    (ha : Continuous a) (ha' : Continuous a') {F : Set (Fin d → ℝ)}
    (hF : ∀ t, ∀ᵐ ω ∂Q, Y t ω ∈ F) (hagree : ∀ y ∈ F ∩ W, a y = a' y) :
    IsMPSolutionOn Q 𝓖 b a' W Y := by
  have hYm : ∀ t, Measurable (Y t) := fun t => ((hY.adapted t).mono (𝓖.le t)).measurable
  set F' : Set (Fin d → ℝ) := Wᶜ ∪ {y | a y = a' y}
  have hF'm : MeasurableSet F' :=
    hW.isClosed_compl.measurableSet.union (isClosed_eq ha ha').measurableSet
  have hF' : ∀ t, ∀ᵐ ω ∂Q, Y t ω ∈ F' := fun t => by
    filter_upwards [hF t] with ω h
    by_cases hw : Y t ω ∈ W
    · exact Or.inr (hagree _ ⟨h, hw⟩)
    · exact Or.inl hw
  have hsl := ae_ae_mem_of_forall hYm hY.continuous hF'm hF'
  refine ⟨hY.adapted, hY.continuous, fun W'' hW'' i => hY.drift W''
    ⟨hW''.1, hW''.2.1, hW''.2.2.trans hWU⟩ i, fun W'' hW'' i j => ?_⟩
  obtain ⟨N, hN, hNe⟩ := hY.bracket W'' ⟨hW''.1, hW''.2.1, hW''.2.2.trans hWU⟩ i j
  refine ⟨N, hN, fun t => (hNe t).trans ?_⟩
  filter_upwards [hsl] with ω hω
  simp only [stoppedProcess_eq_stopTime]
  congr 1
  set s := stopTime (exitTimeFrom W'' Y ω) t
  have hse : ((s : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W'' Y ω :=
    (GeneralIntegral.coe_untopA_min t (exitTimeFrom W'' Y ω)).le.trans (min_le_right _ _)
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ (s : ℝ) := by
    rw [ae_iff]; simp
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hω, hne] with r hr hrs hmem
  have hlt : r < (s : ℝ) := lt_of_le_of_ne hmem.2 hrs
  have hlt' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < exitTimeFrom W'' Y ω := by
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hse
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hmem.1.le]; exact hlt
  have hmW : Y r.toNNReal ω ∈ W :=
    hW''.2.2 (subset_closure (mem_of_lt_exitTimeFrom hlt'))
  rcases hr with h | h
  · exact absurd hmW h
  · exact congrFun (congrFun h i) j

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
