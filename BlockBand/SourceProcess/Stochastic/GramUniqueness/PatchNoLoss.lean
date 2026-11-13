module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankLossCore
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LogBarrierGram
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank loss on whole time intervals

* `markov_cutLog_path`: the Markov estimate `markov_cutLog` with the event `{g(G_{t∧σ_K}) = 0}`
  replaced by `{∃ v ≤ t ∧ σ_K, g(G_v) = 0}` (same proof: on this event the re-stopped log process is again
  `≥ a₁`, because the exit time `τ_ε` from `{ε < g}` is attained before `v`).
* `forall_pos_of_cutLog`: if `g(G_0) > 0` a.s., then a.s. `g(G_v) > 0` for every `v ≤ t ∧ σ_K`.

In the sibling module this gives `GramChart.principalMinorSum_forall_pos`: for a Gram MP solution
with `e_k(B_0) > 0` a.s. (resp. `e_k(M_0 - B_0) > 0`), a.s. `e_k(B_t) > 0`
(resp. `e_k(M_t - B_t) > 0`) for **all** `t`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u

theorem markov_cutLog_path {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hg : ContDiff ℝ 2 g) {ε δ C K E : ℝ}
    (hε : 0 < ε) (hεδ : ε < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hE : 1 ≤ E)
    (hgE : ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → g H ≤ E)
    (hbar : ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → ε ≤ g H →
      gramGenerator D0 D (fun G => cutH ε (g G)) H ≤ C) (t : ℝ≥0) :
    (Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
        ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0}).toReal ≤
      max (Real.log E - Real.log δ + C * t) 0 / (Real.log E - Real.log ε) := by
  set Y : ℝ≥0 → Ω → Fin (gramDim c) → ℝ := fun t ω => toGramReal (G t ω) with hYdef
  have hYm : ∀ t, Measurable[𝓖 t] (Y t) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted t)).measurable
  have hf : ContDiff ℝ 2 fun G => cutH ε (g G) := (contDiff_cutH hε).comp hg
  obtain ⟨N, hN, hNX⟩ := exists_martingale_gramItoProc hD hG hf K
  set ρ' : Ω → WithTop ℝ≥0 := fun ω => min (gramTraceStop G K ω) (lowExit g ε G ω)
  have hρ : IsStoppingTime 𝓖 (fun ω => min (rawHit (traceSuperLevel K) Y ω)
      (rawHit (lowOpen g ε)ᶜ Y ω)) :=
    (isStoppingTime_rawHit hYm).min (isStoppingTime_rawHit hYm)
  have hraw : ∀ᵐ ω ∂Q, rawHit (traceSuperLevel K) Y ω = gramTraceStop G K ω ∧
      rawHit (lowOpen g ε)ᶜ Y ω = lowExit g ε G ω := by
    filter_upwards [hG.continuous] with ω hc
    refine ⟨?_, ?_⟩
    · rw [rawHit_eq_hitTime (Y := Y) (isClosed_traceSuperLevel K) (continuous_toGramReal.comp hc)]
      exact hitTime_traceSuperLevel G K ω
    · rw [rawHit_eq_hitTime (Y := Y) (isOpen_lowOpen hg ε).isClosed_compl
        (continuous_toGramReal.comp hc)]
      rfl
  obtain ⟨M, hM, hMX⟩ := exists_martingale_restrict (X := gramItoProc D0 D _ G) (ρ' := ρ')
    ⟨N, hN, hNX⟩ (by filter_upwards [hG.continuous] with ω hc; exact continuous_gramItoProc D0 D hf hc)
    hρ (by filter_upwards [hraw] with ω h; rw [h.1]; exact min_le_left _ _)
    (by filter_upwards [hraw] with ω h; simp only [ρ', h.1, h.2])
  -- the event `A`
  set A : Set Ω := {ω | δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K}
  have hA : MeasurableSet[𝓖 0] A := by
    have hφ : Measurable[𝓖 0] fun ω => g (fromGramReal (Y 0 ω)) :=
      ((contDiff_comp_fromGramReal hg).continuous.comp_stronglyMeasurable
        (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted 0))).measurable
    have htr : Measurable[𝓖 0] fun ω => ((fromGramReal (Y 0 ω)).1.trace).re :=
      ((Complex.continuous_re.comp ((continuous_fst.comp continuous_fromGramReal').matrix_trace)).comp_stronglyMeasurable
        (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted 0))).measurable
    have e : A = {ω | δ ≤ g (fromGramReal (Y 0 ω))} ∩
        {ω | ((fromGramReal (Y 0 ω)).1.trace).re < K} := by
      ext ω; simp [A, hYdef, fromGramReal_toGramReal]
    rw [e]
    exact (measurableSet_le measurable_const hφ).inter (measurableSet_lt htr measurable_const)
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  -- the constants
  set a0 := -Real.log E + Real.log δ - C * t
  set a1 := -Real.log ε + Real.log δ - C * t
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hgap : a1 - a0 = Real.log E - Real.log ε := by simp only [a0, a1]; ring
  have hgap' : 0 < Real.log E - Real.log ε := by
    have := Real.log_lt_log hε (show ε < E by linarith); linarith
  -- `E[1_A M_t] = 0`
  have hMA : ∫ ω in A, M t ω ∂Q = 0 := by
    rw [← hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) hA]
    refine (integral_congr_ae (ae_restrict_of_ae (hMX 0))).trans ?_
    refine integral_eq_zero_of_ae (ae_of_all _ fun ω => ?_)
    simp [stoppedProcess_eq_stopTime, stopTime_zero, gramItoProc]
  -- pathwise lower bounds
  have hgood : ∀ᵐ ω ∂Q, ω ∈ A → a0 ≤ M t ω ∧
      ((∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0) → a1 ≤ M t ω) := by
    filter_upwards [hMX t, hG.continuous, hG.feasible] with ω hm hc hfe hωA
    rw [hm]
    have hp := cutLog_path_ineq (D0 := D0) hg hε hC hbar hc hfe t
    have hg0 : cutH ε (g (G 0 ω)) ≤ -Real.log δ := by
      rw [cutH_eq hε (by linarith [hωA.1])]
      exact neg_le_neg (Real.log_le_log (by linarith) hωA.1)
    set u := stopTime (min (gramTraceStop G K ω) (lowExit g ε G ω)) t
    have huE : g (G u ω) ≤ E := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hu0
      · rw [← h0]; exact hgE _ (hfe 0) hωA.2.le
      · exact hgE _ (hfe u) (re_trace_le_of_le_stop hc hu0
          ((stopTime_le_self _ t).trans (min_le_left _ _)))
    have hmaxpos : 0 < max (g (G u ω)) (ε / 4) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hlow : -Real.log E ≤ cutH ε (g (G u ω)) :=
      (neg_le_neg (Real.log_le_log hmaxpos (max_le huE (by linarith)))).trans
        (neg_log_le_cutH hε _)
    refine ⟨by simp only [a0]; linarith, fun ⟨v, hv, hz⟩ => ?_⟩
    obtain ⟨s₀, hτ, hs₀v', hs₀⟩ := lowExit_attained (ε := ε) hg hc (v := v)
      (by rw [hz]; exact hε.le)
    have hs₀v : s₀ ≤ stopTime (gramTraceStop G K ω) t := hs₀v'.trans hv
    have hus : u = s₀ := by
      have h1 : min (gramTraceStop G K ω) (lowExit g ε G ω) = s₀ := by
        rw [hτ]; exact min_eq_right ((WithTop.coe_le_coe.2 hs₀v).trans (stopTime_le_self _ t))
      simp only [u, h1, stopTime_coe]
      exact min_eq_right (hs₀v.trans (stopTime_le _ t))
    have hmaxε : max (g (G u ω)) (ε / 4) ≤ ε := max_le (hus ▸ hs₀) (by linarith)
    have hlow' : -Real.log ε ≤ cutH ε (g (G u ω)) :=
      (neg_le_neg (Real.log_le_log hmaxpos hmaxε)).trans (neg_log_le_cutH hε _)
    simp only [a1]; linarith
  -- Markov
  set f : Ω → ℝ := A.indicator fun ω => M t ω - a0
  have hf0 : 0 ≤ᵐ[Q] f := by
    filter_upwards [hgood] with ω h
    by_cases hω : ω ∈ A
    · simp only [f, Set.indicator_of_mem hω, Pi.zero_apply]; linarith [(h hω).1]
    · simp only [f, Set.indicator_of_notMem hω, Pi.zero_apply, le_refl]
  have hfi : Integrable f Q := ((hM.integrable t).sub (integrable_const a0)).indicator hA'
  have hmk := mul_meas_ge_le_integral_of_nonneg hf0 hfi (a1 - a0)
  have hint : ∫ ω, f ω ∂Q = -a0 * Q.real A := by
    rw [integral_indicator hA', integral_sub (hM.integrable t).integrableOn (integrable_const _),
      hMA, setIntegral_const, smul_eq_mul]
    ring
  have hqA : Q.real A ≤ 1 := (measureReal_mono (subset_univ A)).trans (by simp)
  have hq0 : 0 ≤ Q.real A := measureReal_nonneg
  have hint' : ∫ ω, f ω ∂Q ≤ max (Real.log E - Real.log δ + C * t) 0 := by
    rw [hint]
    have : -a0 = Real.log E - Real.log δ + C * t := by simp only [a0]; ring
    rw [this]
    rcases le_total 0 (Real.log E - Real.log δ + C * t) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  have hsub : Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
      ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0} ≤
        Q {ω | a1 - a0 ≤ f ω} := by
    refine measure_mono_ae ?_
    filter_upwards [hgood] with ω h hS
    have hS' : ω ∈ A ∧ ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0 := hS
    show a1 - a0 ≤ f ω
    simp only [f, Set.indicator_of_mem hS'.1]
    linarith [(h hS'.1).2 hS'.2]
  have hT : (Q {ω | a1 - a0 ≤ f ω}).toReal ≤
      max (Real.log E - Real.log δ + C * t) 0 / (Real.log E - Real.log ε) := by
    rw [le_div_iff₀ hgap', ← hgap, mul_comm]
    exact hmk.trans hint'
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans hT

theorem forall_pos_of_cutLog {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgpos : ∀ H, GramFeasible D H → 0 ≤ g H) {K C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ ε, 0 < ε → ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → ε ≤ g H →
      gramGenerator D0 D (fun G => cutH ε (g G)) H ≤ C)
    (h0 : ∀ᵐ ω ∂Q, 0 < g (G 0 ω)) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t → 0 < g (G v ω) := by
  obtain ⟨E, hE, hgE⟩ := exists_feasible_bound (D := D) hg K
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hnull : ∀ j : ℕ, Q {ω | ((1 / ((j : ℝ) + 2)) ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
      ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0} = 0 := by
    intro j
    set δ : ℝ := 1 / ((j : ℝ) + 2)
    have hδ : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
    set c0 := max (Real.log E - Real.log δ + C * t) 0
    have hc0 : 0 ≤ c0 := le_max_right _ _
    have hb : ∀ n : ℕ, (Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
        ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0}).toReal ≤
          c0 / ((n : ℝ) + 1) := by
      intro n
      set ε := δ * Real.exp (-((n : ℝ) + 1))
      have hε : 0 < ε := by positivity
      have hεδ : ε < δ := by
        have : Real.exp (-((n : ℝ) + 1)) < 1 :=
          Real.exp_lt_one_iff.2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        nlinarith
      refine (markov_cutLog_path hD hG hg hε hεδ hδ1 hC hE hgE (hbar ε hε) t).trans ?_
      have hlogε : Real.log ε = Real.log δ - ((n : ℝ) + 1) := by
        rw [Real.log_mul hδ.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
      rw [hlogε]
      exact div_le_div_of_nonneg_left hc0 (by positivity) (by linarith)
    have hz : (Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
        ∃ v : ℝ≥0, v ≤ stopTime (gramTraceStop G K ω) t ∧ g (G v ω) = 0}).toReal = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun x hx => ?_) ENNReal.toReal_nonneg
      obtain ⟨n, hn⟩ := exists_nat_gt (c0 / x)
      refine (hb n).trans ?_
      rw [zero_add, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hx] at hn
      nlinarith
    exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right (measure_ne_top _ _)
  have hall := ae_all_iff.2 fun j => measure_eq_zero_iff_ae_notMem.1 (hnull j)
  filter_upwards [hall, h0, hG.feasible] with ω hj hpos hfe v hv
  rcases le_or_gt K ((G 0 ω).1.trace).re with hK | hK
  · have h0' : gramTraceStop G K ω = 0 := le_antisymm (iInf₂_le (0 : ℝ≥0) hK) bot_le
    rw [h0', stopTime_of_eq_zero] at hv
    rw [le_antisymm hv zero_le]; exact hpos
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have hδ : 1 / ((n : ℝ) + 2) ≤ g (G 0 ω) := by
      refine le_trans ?_ hn.le
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hne := hj n
    exact lt_of_le_of_ne (hgpos _ (hfe _)) (Ne.symm fun h => hne ⟨⟨hδ, hK⟩, v, hv, h⟩)

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
