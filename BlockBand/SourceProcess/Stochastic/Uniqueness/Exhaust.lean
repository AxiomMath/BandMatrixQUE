module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.SetupMP
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localize
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Tools for stopped-law uniqueness with positive definite covariance

Lemmas used in the proof of `StoppedMartingaleProblemUniquenessPosDef`.

* `isMPSolutionOn_congr`: the martingale problem only sees the covariance on the domain.
* `aemeasurable_stopped`: the stopped path `ω ↦ (t ↦ Y_{t ∧ τ_W})` of an adapted a.s.
  continuous process is a.e.-measurable into the product `ℝ≥0 → ℝ^d` (version through a raw
  hitting time and a joint version; no modification of `Y`).
* `tendsto_stopped_exhaust`: along the exhaustion `exhaust W m` of an open `W`, the stopped
  values `Y_{t ∧ τ_m}` of a continuous path converge to `Y_{t ∧ τ_W}`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal ENNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem isMPSolutionOn_congr {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a a' : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U : Set (Fin d → ℝ)}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : IsMPSolutionOn Q 𝓖 b a U Y) (haa : EqOn a a' U) :
    IsMPSolutionOn Q 𝓖 b a' U Y := by
  refine ⟨hY.adapted, hY.continuous, hY.drift, fun W hW i j => ?_⟩
  obtain ⟨N, hN, hNe⟩ := hY.bracket W hW i j
  refine ⟨N, hN, fun t => (hNe t).trans ?_⟩
  filter_upwards [hY.continuous] with ω hω
  simp only [stoppedProcess_eq_stopTime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [haa (hW.2.2 ((stopped_path_mem_closure hW.1 hω t).1 s hs))]

omit [MeasurableSpace Ω] in
theorem exitTimeFrom_mono {W₁ W₂ : Set (Fin d → ℝ)} (h : W₁ ⊆ W₂) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (ω : Ω) : exitTimeFrom W₁ Y ω ≤ exitTimeFrom W₂ Y ω :=
  le_iInf₂ fun t ht => iInf₂_le t fun h' => ht (h h')

omit [MeasurableSpace Ω] in
theorem coe_stopTime (e : WithTop ℝ≥0) (t : ℝ≥0) :
    ((stopTime e t : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) e :=
  GeneralIntegral.coe_untopA_min t e

omit [MeasurableSpace Ω] in
theorem stopTime_mono {e e' : WithTop ℝ≥0} (h : e ≤ e') (t : ℝ≥0) :
    stopTime e t ≤ stopTime e' t := by
  rw [← WithTop.coe_le_coe, coe_stopTime, coe_stopTime]
  exact min_le_min le_rfl h

omit [MeasurableSpace Ω] in
/-- **Exhaustion of the stopped values.** -/
theorem tendsto_stopped_exhaust {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hc : Continuous fun t => Y t ω) (t : ℝ≥0) :
    Tendsto (fun m => Y (stopTime (exitTimeFrom (exhaust W m) Y ω) t) ω) atTop
      (𝓝 (Y (stopTime (exitTimeFrom W Y ω) t) ω)) := by
  set s : ℕ → ℝ≥0 := fun m => stopTime (exitTimeFrom (exhaust W m) Y ω) t
  set s' := stopTime (exitTimeFrom W Y ω) t
  have hsub : ∀ m, exhaust W m ⊆ W := fun m =>
    subset_closure.trans (closure_exhaust_subset_U (U := W) m)
  have hmono : Monotone s := fun m m' h =>
    stopTime_mono (exitTimeFrom_mono (exhaust_mono h) Y ω) t
  have hle : ∀ m, s m ≤ s' := fun m => stopTime_mono (exitTimeFrom_mono (hsub m) Y ω) t
  have hbdd : BddAbove (range s) := ⟨s', by rintro _ ⟨m, rfl⟩; exact hle m⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ m, s m
  have hL : L = s' := by
    refine le_antisymm (ciSup_le hle) ?_
    by_contra hlt
    push Not at hlt
    have hst : s' ≤ t := stopTime_le _ _
    have hLe : (L : WithTop ℝ≥0) < exitTimeFrom W Y ω := by
      have h1 : ((s' : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω := by
        rw [coe_stopTime]; exact min_le_right _ _
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hlt) h1
    have hmem : Y L ω ∈ W := mem_of_lt_exitTimeFrom hLe
    rw [← iUnion_exhaust hW, mem_iUnion] at hmem
    obtain ⟨m₀, hm₀⟩ := hmem
    have hO : ∀ᶠ m in atTop, Y (s m) ω ∈ exhaust W m₀ :=
      hlim.eventually ((isOpen_exhaust m₀).preimage hc |>.mem_nhds hm₀)
    obtain ⟨m, hm, hmm⟩ := (hO.and (eventually_ge_atTop m₀)).exists
    have hsm : s m < t := lt_of_le_of_lt (le_ciSup hbdd m) (lt_of_lt_of_le hlt hst)
    have he : exitTimeFrom (exhaust W m) Y ω = (s m : WithTop ℝ≥0) := by
      have := coe_stopTime (exitTimeFrom (exhaust W m) Y ω) t
      rw [this]
      rcases le_total (t : WithTop ℝ≥0) (exitTimeFrom (exhaust W m) Y ω) with h | h
      · exfalso
        have h2 : ((s m : ℝ≥0) : WithTop ℝ≥0) = t := by
          change ((stopTime _ t : ℝ≥0) : WithTop ℝ≥0) = t
          rw [coe_stopTime, min_eq_left h]
        exact absurd (WithTop.coe_injective h2) hsm.ne
      · rw [min_eq_right h]
    rcases exitTimeFrom_attained (isOpen_exhaust m) hc with h | ⟨s₀, hs₀, hns⟩
    · rw [he] at h; exact WithTop.coe_ne_top h
    · rw [he, WithTop.coe_inj] at hs₀
      rw [← hs₀] at hns
      exact hns (exhaust_mono hmm hm)
  rw [hL] at hlim
  exact (hc.tendsto s').comp hlim

/-- **The stopped path is a.e.-measurable into the path space.** -/
theorem aemeasurable_stopped {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : ∀ t, Measurable[𝓖 t] (Y t))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) {W : Set (Fin d → ℝ)} (hW : IsOpen W) :
    AEMeasurable (fun ω t => stoppedProcess Y (exitTimeFrom W Y) t ω) Q := by
  obtain ⟨τ, hτ, hτc, -⟩ := exists_stoppingTime_ae_eq_hitTime hY hc hW.isClosed_compl
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set hc
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY t).mono (𝓖.le t) le_rfl
  refine ⟨fun ω t => jointVersion Y A ((stopTime (τ ω) t : ℝ), ω), Measurable.of_eval fun t =>
    (measurable_jointVersion hYm hA hAc).comp ((Measurable.untopA (measurable_const.min
      hτ.measurable')).coe_nnreal_real.prodMk measurable_id), ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω hω
  have hω' : ω ∈ A := by simpa using hω
  funext t
  simp only [stoppedProcess_eq_stopTime, jointVersion_of_mem hω', Real.toNNReal_coe]
  rw [hτc ω (hAc ω hω')]
  rfl

end BlockBand.SourceProcess.Stochastic.Uniqueness
