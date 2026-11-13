module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Local
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The localizing sequence for the Itô formula)

For a contract semimartingale `Y` (characteristics `β, α`, localizer `τ_m`) with values a.s.
in the open `U`, and `φ` Borel, `C²` on `univ ×ˢ U`:

`σ_m = min(τ_m, ρE_m, ρV_m, m)` on `{Y_0 ∈ W_m}` and `0` off it, where `W_m = exhaust U m`,
`ρE_m` is a raw stopping time equal to the exit time from `W_m` on continuous paths, and `ρV_m`
a raw stopping time equal on continuous paths to the hitting time of `[m, ∞)` by the control
`V_t = ∫_0^t (Σ|β^i| + Σ|α^{ij}|)` (adapted for every `ω` by Fubini, continuous a.s.).

`exists_localizer`: the `σ_m` are stopping times, `σ_m → ⊤` a.s., each satisfies `LocData` (with
`T = c = m`), and the `σ_m`-stopped compensated coordinates and products of `Y` have martingale
modifications (optional stopping `exists_martingale_stoppedProcess` applied to the
`τ_m`-stopped ones, `σ_m ≤ τ_m`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ}

theorem stoppedProcess_stop_of_le {E : Type*} (X : ℝ≥0 → Ω → E) {τ σ : Ω → WithTop ℝ≥0}
    (h : ∀ ω, σ ω ≤ τ ω) : stoppedProcess (stoppedProcess X τ) σ = stoppedProcess X σ := by
  funext t ω
  simp only [stoppedProcess_eq_stopTime]
  rw [stopTime_eq_of_le ((stopTime_le_self _ t).trans (h ω))]

theorem hasMartingaleModification_stop_of_le [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {τ σ : Ω → WithTop ℝ≥0}
    (hX : HasMartingaleModification Q 𝓖 (stoppedProcess X τ))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X τ t ω) (hσ : IsStoppingTime 𝓖 σ)
    (h : ∀ ω, σ ω ≤ τ ω) : HasMartingaleModification Q 𝓖 (stoppedProcess X σ) := by
  obtain ⟨M, hM, hMX⟩ := hX
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc hσ
  exact ⟨M', hM', fun t => by rw [← stoppedProcess_stop_of_le X h]; exact hM'X t⟩

/-- **The localizing sequence.** -/
theorem exists_localizer [IsProbabilityMeasure Q] (H : IsContinuousSemimartingale Q 𝓖 Y β α) (hU : IsOpen U)
    (hYU : ∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U) (hφm : Measurable φ) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U)) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ m, IsStoppingTime 𝓖 (σ m)) ∧
      (∀ᵐ ω ∂Q, Tendsto (fun m => σ m ω) atTop (𝓝 ⊤)) ∧ ∀ m,
        (∃ (W : Set (Fin d → ℝ)) (T : ℝ≥0) (c : ℝ) (ys : Fin d → ℝ),
          LocData Q 𝓖 Y β α U W φ (σ m) T c ys) ∧
        (∀ i, HasMartingaleModification Q 𝓖 (stoppedProcess (smCompensated Y β i) (σ m))) ∧
        ∀ i j, HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
          smCompensated Y β i t ω * smCompensated Y β j t ω -
            ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j) (σ m)) := by
  classical
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  obtain ⟨ω₀, hω₀⟩ := hYU.exists
  set ys := Y 0 ω₀
  have hys : ys ∈ U := hω₀ 0
  have hYm : ∀ t, Measurable[𝓖 t] (Y t) := fun t => (H.adapted t).measurable
  -- the control and its level stops
  set V : ℝ≥0 → Ω → ℝ := fun t ω => ctrlI β (matF α) t ω
  have hVm : ∀ t, Measurable[𝓖 t] (V t) := fun t =>
    (stronglyMeasurable_integral_of_progressive
      (isStronglyProgressive_ctrl H.drift_progressive H.cov_progressive) t).measurable
  have hVc : ∀ ω, (∀ t : ℝ≥0, (∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t)) ∧
      ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Ioc 0 t)) →
      Continuous fun t => V t ω := fun ω hi =>
    continuous_setIntegral_Ioc (g := fun u => ctrl β (matF α) u ω) fun u => by
      unfold ctrl matF
      exact Integrable.add (integrable_finsetSum _ fun i _ => ((hi u).1 i).abs)
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ((hi u).2 i j).abs)
  have hVcae : ∀ᵐ ω ∂Q, Continuous fun t => V t ω := H.integrable.mono hVc
  choose ρV hρV hρVeq _ using fun m : ℕ =>
    exists_stoppingTime_ae_eq_hitTime (𝓖 := 𝓖) (Q := Q) hVm hVcae (isClosed_Ici (a := (m : ℝ)))
  choose ρE hρE hρEeq _ using fun m : ℕ =>
    exists_stoppingTime_ae_eq_hitTime (𝓖 := 𝓖) (Q := Q) hYm H.continuous
      (isOpen_exhaust (U := U) m).isClosed_compl
  set σ₀ : ℕ → Ω → WithTop ℝ≥0 := fun m ω =>
    min (min (τ m ω) (ρE m ω)) (min (ρV m ω) ((m : ℝ≥0) : WithTop ℝ≥0))
  have hσ₀ : ∀ m, IsStoppingTime 𝓖 (σ₀ m) := fun m =>
    ((hτ m).min (hρE m)).min ((hρV m).min (isStoppingTime_const 𝓖 _))
  set σ : ℕ → Ω → WithTop ℝ≥0 := fun m ω => if Y 0 ω ∈ exhaust U m then σ₀ m ω else 0
  have hG : ∀ m, MeasurableSet[𝓖 0] {ω | Y 0 ω ∈ exhaust U m} := fun m =>
    (hYm 0) (isOpen_exhaust m).measurableSet
  have hσ : ∀ m, IsStoppingTime 𝓖 (σ m) := by
    intro m t
    have e : {ω | σ m ω ≤ t} = ({ω | Y 0 ω ∈ exhaust U m} ∩ {ω | σ₀ m ω ≤ t}) ∪
        {ω | Y 0 ω ∈ exhaust U m}ᶜ := by
      ext ω
      by_cases h : Y 0 ω ∈ exhaust U m
      · simp [σ, h]
      · simp only [σ, h, ↓reduceIte, mem_union, mem_compl_iff, mem_ofPred_eq, not_false_eq_true,
          or_true, iff_true]
        exact zero_le
    rw [e]
    have hGt : MeasurableSet[𝓖 t] {ω | Y 0 ω ∈ exhaust U m} := 𝓖.mono zero_le _ (hG m)
    exact (hGt.inter (hσ₀ m t)).union hGt.compl
  have hστ : ∀ m ω, σ m ω ≤ τ m ω := fun m ω => by
    simp only [σ]; split_ifs
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact zero_le
  refine ⟨σ, hσ, ?_, fun m => ⟨⟨exhaust U m, m, m, ys, ?_⟩, fun i => ?_, fun i j => ?_⟩⟩
  · -- σ → ⊤
    filter_upwards [hτlim, H.continuous, hYU, hVcae] with ω h1 h2 h3 h4
    have hE : Tendsto (fun m => ρE m ω) atTop (𝓝 ⊤) := by
      refine (tendsto_exitTimeFrom_exhaust hU h2 h3).congr fun m => ?_
      have e : ρE m ω = exitTimeFrom (exhaust U m) Y ω := (hρEeq m) ω h2
      exact e.symm
    have hV : Tendsto (fun m => ρV m ω) atTop (𝓝 ⊤) := by
      refine (tendsto_hitTime_Ici_top h4).congr fun m => ?_
      exact ((hρVeq m) ω h4).symm
    have hN : Tendsto (fun m : ℕ => ((m : ℝ≥0) : WithTop ℝ≥0)) atTop (𝓝 ⊤) :=
      WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun m => σ₀ m ω) atTop (𝓝 ⊤) := by
      have := (h1.min hE).min (hV.min hN)
      simpa only [min_self] using this
    obtain ⟨m₁, hm₁⟩ := exists_exhaust_of_compact hU (isCompact_singleton (x := Y 0 ω))
      (singleton_subset_iff.2 (h3 0))
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop m₁] with m hm
    simp only [σ, exhaust_mono hm (hm₁ rfl), ↓reduceIte]
  · -- the localization data
    refine ⟨H, hU, hYU, hφm, hφ, isOpen_exhaust m, isCompact_closure_exhaust m,
      closure_exhaust_subset_U m, hys, hσ m, fun ω => ?_, fun ω h => ?_, ?_, ?_⟩
    · simp only [σ]; split_ifs
      · exact (min_le_right _ _).trans (min_le_right _ _)
      · exact zero_le
    · simp only [σ, h, ↓reduceIte]
    · filter_upwards [H.continuous] with ω hω h0 t
      have hle : σ m ω ≤ exitTimeFrom (exhaust U m) Y ω := by
        have e : ρE m ω = exitTimeFrom (exhaust U m) Y ω := (hρEeq m) ω hω
        rw [← e]
        simp only [σ, h0, ↓reduceIte]
        exact (min_le_left _ _).trans (min_le_right _ _)
      have := stop_mem_closure (isOpen_exhaust m) hω h0 (stopTime (σ m ω) t)
      rwa [stopTime_eq_of_le ((stopTime_le_self _ t).trans hle)] at this
    · filter_upwards [hVcae] with ω hω t
      by_cases h0 : Y 0 ω ∈ exhaust U m
      · have hle : σ m ω ≤ hitTime (Ici (m : ℝ)) V ω := by
          rw [← (hρVeq m) ω hω]
          simp only [σ, h0, ↓reduceIte]
          exact (min_le_right _ _).trans (min_le_left _ _)
        have hV0 : V 0 ω ≤ (m : ℝ) := by
          simp [V, ctrlI]
        exact le_of_le_hitTime_Ici hω hV0 ((stopTime_le_self _ t).trans hle)
      · simp only [σ, h0, ↓reduceIte, stopTime_of_eq_zero']
        simp [ctrlI]
  · -- compensated coordinates
    refine hasMartingaleModification_stop_of_le ((hmart m).1 i) ?_ (hσ m) (hστ m)
    filter_upwards [H.continuous, H.integrable] with ω hω hi
    exact (continuous_smCompensated hω fun t => (hi t).1 i).comp (continuous_stopTime _)
  · -- compensated products
    refine hasMartingaleModification_stop_of_le ((hmart m).2 i j) ?_ (hσ m) (hστ m)
    filter_upwards [H.continuous, H.integrable] with ω hω hi
    exact (((continuous_smCompensated hω fun t => (hi t).1 i).mul
      (continuous_smCompensated hω fun t => (hi t).1 j)).sub
      (continuous_setIntegral_Ioc (g := fun u => α u ω i j) fun t => (hi t).2 i j)).comp
      (continuous_stopTime _)

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
