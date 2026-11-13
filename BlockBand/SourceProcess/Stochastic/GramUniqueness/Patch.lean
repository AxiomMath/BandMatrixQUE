module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LocalUniq
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.PatchNoLoss
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Patching the charts: Gram-law uniqueness on a fixed stratum

* `principalMinorSum_forall_pos`: no rank loss at any time (`forall_pos_of_cutLog` over all
  integer horizons and trace levels).
* `eventually_le_exit`: along a path that keeps `e_r(B) > 0` and `e_{r'}(M - B) > 0` at all times,
  the exit times from `chartDom r r' (1/(n+1)) (n+1)` eventually exceed every `t` (compactness of
  `[0, t]`: the trace is bounded and `e_r`, `e_{r'}` have positive minima).
* **`gramLaw_eq_of_stratum`**: two Gram MP solutions (sample spaces in any universes), with
  `0 < D₀`, a signature `𝖣`, equal initial laws and initial states a.s. on the stratum
  `{e_r(B) > 0, e_{r+1}(B) = 0, e_{r'}(M - B) > 0, e_{r'+1}(M - B) = 0}`, have equal path laws on
  `ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ`. The chart stopped laws agree (`chart_stopped_law_eq`),
  the stopped paths converge to the paths (no rank creation; pathwise no rank loss; trace
  localization), then finite-dimensional laws (`map_eq_of_tendsto_ae`,
  `map_eq_of_fdd_eq₂'`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u v

omit [DecidableEq c] in
theorem forall_pos_of_horizons {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} {ω : Ω} (hc : Continuous fun t => G t ω)
    (h : ∀ K T : ℕ, ∀ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) T → 0 < g (G v ω)) (t : ℝ≥0) :
    0 < g (G t ω) := by
  obtain ⟨T, hT⟩ := exists_nat_ge (t : ℝ)
  have htT : t ≤ (T : ℝ≥0) := by exact_mod_cast hT
  obtain ⟨K, hK⟩ := exists_lt_gramTraceStop hc (T : ℝ≥0)
  exact h K T t (by rw [stopTime_of_le hK]; exact htT)

/-- **No rank loss at any time.** -/
theorem principalMinorSum_forall_pos {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
    (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    (k : ℕ) :
    ((∀ᵐ ω ∂Q, 0 < principalMinorSum k (G 0 ω).2) →
      ∀ᵐ ω ∂Q, ∀ t, 0 < principalMinorSum k (G t ω).2) ∧
    ((∀ᵐ ω ∂Q, 0 < principalMinorSum k ((G 0 ω).1 - (G 0 ω).2)) →
      ∀ᵐ ω ∂Q, ∀ t, 0 < principalMinorSum k ((G t ω).1 - (G t ω).2)) := by
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have h := fun K T : ℕ => forall_pos_of_cutLog (K := (K : ℝ))
      (g := fun H => principalMinorSum k H.2) hD hG (contDiff_ek_snd k)
      (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).1)
      (by unfold logNearConst; positivity)
      (fun ε hε H hH hK => (gramGenerator_cutLog_le hD0 hD k K hε hH hK).1) h0 (T : ℝ≥0)
    filter_upwards [ae_all_iff.2 fun K => ae_all_iff.2 (h K), hG.continuous] with ω hω hc
    exact forall_pos_of_horizons (g := fun H => principalMinorSum k H.2) hc hω
  · have h := fun K T : ℕ => forall_pos_of_cutLog (K := (K : ℝ))
      (g := fun H => principalMinorSum k (H.1 - H.2)) hD hG (contDiff_ek_fst_sub_snd k)
      (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).2)
      (by unfold logFarConst; positivity)
      (fun ε hε H hH hK => (gramGenerator_cutLog_le hD0 hD k K hε hH hK).2) h0 (T : ℝ≥0)
    filter_upwards [ae_all_iff.2 fun K => ae_all_iff.2 (h K), hG.continuous] with ω hω hc
    exact forall_pos_of_horizons (g := fun H => principalMinorSum k (H.1 - H.2)) hc hω

/-- The chart domains of the exhaustion. -/
def chartSeq (c : Type*) [Fintype c] [DecidableEq c] (r r' n : ℕ) : Set (Fin (gramDim c) → ℝ) :=
  chartDom c r r' (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)

theorem eventually_le_exit {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω}
    (hc : Continuous fun t => G t ω) {r r' : ℕ}
    (hB : ∀ t, 0 < principalMinorSum r (G t ω).2)
    (hC : ∀ t, 0 < principalMinorSum r' ((G t ω).1 - (G t ω).2)) (t : ℝ≥0) :
    ∀ᶠ n in atTop, (t : WithTop ℝ≥0) ≤
      exitTimeFrom (chartSeq c r r' n) (fun t ω => toGramReal (G t ω)) ω := by
  have hI : IsCompact (Icc (0 : ℝ≥0) t) := isCompact_Icc
  have hne : (Icc (0 : ℝ≥0) t).Nonempty := ⟨0, zero_le, zero_le⟩
  have hfB : Continuous fun s => principalMinorSum r (G s ω).2 := (contDiff_ek_snd r).continuous.comp hc
  have hfC : Continuous fun s => principalMinorSum r' ((G s ω).1 - (G s ω).2) :=
    (contDiff_ek_fst_sub_snd r').continuous.comp hc
  have hY : Continuous fun s => toGramReal (G s ω) := continuous_toGramReal.comp hc
  obtain ⟨sB, -, hsB⟩ := hI.exists_isMinOn hne hfB.continuousOn
  obtain ⟨sC, -, hsC⟩ := hI.exists_isMinOn hne hfC.continuousOn
  obtain ⟨R, hR⟩ := hI.exists_bound_of_continuousOn hY.continuousOn
  set m := min (principalMinorSum r (G sB ω).2) (principalMinorSum r' ((G sC ω).1 - (G sC ω).2))
  have hm : 0 < m := lt_min (hB sB) (hC sC)
  obtain ⟨N, hN⟩ := exists_nat_gt (max R (1 / m))
  refine eventually_atTop.2 ⟨N, fun n hn => le_iInf₂ fun s hs => WithTop.coe_le_coe.2 ?_⟩
  by_contra hst
  have hsI : s ∈ Icc (0 : ℝ≥0) t := ⟨zero_le, (not_le.1 hst).le⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hη : 1 / ((n : ℝ) + 1) < m := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 / m < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    rw [div_lt_iff₀ hm] at h1
    nlinarith
  refine hs ⟨?_, ?_, ?_⟩
  · have := hR s hsI
    linarith [le_max_left R (1 / m)]
  · simp only [fromGramReal_toGramReal]
    exact lt_of_lt_of_le hη ((min_le_left _ _).trans (hsB hsI))
  · simp only [fromGramReal_toGramReal]
    exact lt_of_lt_of_le hη ((min_le_right _ _).trans (hsC hsI))

/-- **Gram-law uniqueness on a fixed stratum.** -/
theorem gramLaw_eq_of_stratum {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {r r' : ℕ}
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {G₁ : ℝ≥0 → Ω₁ → Matrix c c ℂ × Matrix c c ℂ} (hG₁ : IsGramMartingaleSolution Q₁ 𝓖₁ D0 D G₁)
    (hBz₁ : ∀ᵐ ω ∂Q₁, principalMinorSum (r + 1) (G₁ 0 ω).2 = 0)
    (hBp₁ : ∀ᵐ ω ∂Q₁, 0 < principalMinorSum r (G₁ 0 ω).2)
    (hCz₁ : ∀ᵐ ω ∂Q₁, principalMinorSum (r' + 1) ((G₁ 0 ω).1 - (G₁ 0 ω).2) = 0)
    (hCp₁ : ∀ᵐ ω ∂Q₁, 0 < principalMinorSum r' ((G₁ 0 ω).1 - (G₁ 0 ω).2))
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {G₂ : ℝ≥0 → Ω₂ → Matrix c c ℂ × Matrix c c ℂ} (hG₂ : IsGramMartingaleSolution Q₂ 𝓖₂ D0 D G₂)
    (hBz₂ : ∀ᵐ ω ∂Q₂, principalMinorSum (r + 1) (G₂ 0 ω).2 = 0)
    (hBp₂ : ∀ᵐ ω ∂Q₂, 0 < principalMinorSum r (G₂ 0 ω).2)
    (hCz₂ : ∀ᵐ ω ∂Q₂, principalMinorSum (r' + 1) ((G₂ 0 ω).1 - (G₂ 0 ω).2) = 0)
    (hCp₂ : ∀ᵐ ω ∂Q₂, 0 < principalMinorSum r' ((G₂ 0 ω).1 - (G₂ 0 ω).2))
    (h0 : Q₁.map (G₁ 0) = Q₂.map (G₂ 0)) :
    Q₁.map (fun ω t => G₁ t ω) = Q₂.map (fun ω t => G₂ t ω) := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := Prod.borelSpace
  set Y₁ : ℝ≥0 → Ω₁ → Fin (gramDim c) → ℝ := fun t ω => toGramReal (G₁ t ω)
  set Y₂ : ℝ≥0 → Ω₂ → Fin (gramDim c) → ℝ := fun t ω => toGramReal (G₂ t ω)
  have hYa₁ : ∀ t, Measurable[𝓖₁ t] (Y₁ t) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG₁.adapted t)).measurable
  have hYa₂ : ∀ t, Measurable[𝓖₂ t] (Y₂ t) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG₂.adapted t)).measurable
  have hYc₁ : ∀ᵐ ω ∂Q₁, Continuous fun t => Y₁ t ω := by
    filter_upwards [hG₁.continuous] with ω h using continuous_toGramReal.comp h
  have hYc₂ : ∀ᵐ ω ∂Q₂, Continuous fun t => Y₂ t ω := by
    filter_upwards [hG₂.continuous] with ω h using continuous_toGramReal.comp h
  have hpath₁ : ∀ᵐ ω ∂Q₁, ∀ t : ℝ≥0, ∀ᶠ n in atTop,
      (t : WithTop ℝ≥0) ≤ exitTimeFrom (chartSeq c r r' n) Y₁ ω := by
    filter_upwards [hG₁.continuous, (principalMinorSum_forall_pos hD0 hD hG₁ r).1 hBp₁,
      (principalMinorSum_forall_pos hD0 hD hG₁ r').2 hCp₁] with ω hc hb hcc t
    exact eventually_le_exit hc hb hcc t
  have hpath₂ : ∀ᵐ ω ∂Q₂, ∀ t : ℝ≥0, ∀ᶠ n in atTop,
      (t : WithTop ℝ≥0) ≤ exitTimeFrom (chartSeq c r r' n) Y₂ ω := by
    filter_upwards [hG₂.continuous, (principalMinorSum_forall_pos hD0 hD hG₂ r).1 hBp₂,
      (principalMinorSum_forall_pos hD0 hD hG₂ r').2 hCp₂] with ω hc hb hcc t
    exact eventually_le_exit hc hb hcc t
  have hW : ∀ n, IsOpen (chartSeq c r r' n) := fun n => (isInteriorDomain_chartDom _ _ _ _).1
  have hfdd : ∀ I : Finset ℝ≥0, Q₁.map (fun ω => I.restrict fun t => Y₁ t ω) =
      Q₂.map (fun ω => I.restrict fun t => Y₂ t ω) := by
    intro I
    refine map_eq_of_tendsto_ae
      (f₁ := fun n ω => I.restrict fun t =>
        stoppedProcess Y₁ (exitTimeFrom (chartSeq c r r' n) Y₁) t ω)
      (f₂ := fun n ω => I.restrict fun t =>
        stoppedProcess Y₂ (exitTimeFrom (chartSeq c r r' n) Y₂) t ω)
      (fun n => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₁ hYc₁ (hW n)))
      (fun n => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₂ hYc₂ (hW n))) ?_ ?_ fun n => ?_
    · filter_upwards [hpath₁] with ω hω
      refine tendsto_pi_nhds.2 fun t => tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      simp only [Finset.restrict, stoppedProcess_eq_stopTime, stopTime_of_le hn]
    · filter_upwards [hpath₂] with ω hω
      refine tendsto_pi_nhds.2 fun t => tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      simp only [Finset.restrict, stoppedProcess_eq_stopTime, stopTime_of_le hn]
    · have hl := chart_stopped_law_eq hD0 hD (η := 1 / ((n : ℝ) + 1)) (K := (n : ℝ) + 1)
        (by positivity) (by positivity) hG₁ hBz₁ hCz₁ hG₂ hBz₂ hCz₂ h0
      have e₁ := AEMeasurable.map_map_of_aemeasurable
        (Finset.measurable_restrict (X := fun _ : ℝ≥0 => Fin (gramDim c) → ℝ) I).aemeasurable
        (aemeasurable_stopped hYa₁ hYc₁ (hW n))
      have e₂ := AEMeasurable.map_map_of_aemeasurable
        (Finset.measurable_restrict (X := fun _ : ℝ≥0 => Fin (gramDim c) → ℝ) I).aemeasurable
        (aemeasurable_stopped hYa₂ hYc₂ (hW n))
      have hl' : Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom (chartSeq c r r' n) Y₁) t ω) =
          Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom (chartSeq c r r' n) Y₂) t ω) := hl
      exact e₁.symm.trans ((congrArg (fun μ => μ.map I.restrict) hl').trans e₂)
  have hYm₁ : Measurable fun ω t => Y₁ t ω := Measurable.of_eval fun t => (hYa₁ t).mono (𝓖₁.le t) le_rfl
  have hYm₂ : Measurable fun ω t => Y₂ t ω := Measurable.of_eval fun t => (hYa₂ t).mono (𝓖₂.le t) le_rfl
  have hY := map_eq_of_fdd_eq₂' hYm₁.aemeasurable hYm₂.aemeasurable hfdd
  have hF : Measurable fun (f : ℝ≥0 → Fin (gramDim c) → ℝ) (t : ℝ≥0) => fromGramReal (f t) :=
    Measurable.of_eval fun t => continuous_fromGramReal'.measurable.comp (measurable_pi_apply t)
  have e₁ : (fun ω t => G₁ t ω) = (fun (f : ℝ≥0 → Fin (gramDim c) → ℝ) t => fromGramReal (f t)) ∘
      (fun ω t => Y₁ t ω) := by
    funext ω t; simp [Y₁, fromGramReal_toGramReal]
  have e₂ : (fun ω t => G₂ t ω) = (fun (f : ℝ≥0 → Fin (gramDim c) → ℝ) t => fromGramReal (f t)) ∘
      (fun ω t => Y₂ t ω) := by
    funext ω t; simp [Y₂, fromGramReal_toGramReal]
  rw [e₁, e₂, ← Measure.map_map hF hYm₁, ← Measure.map_map hF hYm₂, hY]

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
