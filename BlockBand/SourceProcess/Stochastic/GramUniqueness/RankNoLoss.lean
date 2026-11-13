module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankLossCore
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LogBarrierGram
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank loss: neither Gram rank can decrease before the trace stop

For every feasible Gram martingale-problem solution (sample space in any universe), `0 < D₀`,
a signature `𝖣`, `k`, `K`: if `e_k(B_0) > 0` a.s. then `e_k(B_{t∧σ_K}) > 0` a.s. for every `t`
(`principalMinorSum_near_stopped_pos`), and likewise for `M − B`
(`principalMinorSum_far_stopped_pos`). This is the paper's "no rank loss at finite time"
for every solution, not only the ambient one. It is proved from the log barrier
(`gramGenerator_cutLog_le`) and the Markov estimate (`markov_cutLog`) with
`ε_n = δ e^{−(n+1)} → 0` and `δ = 1/(j+2) → 0`. The generic form is `stopped_pos_of_cutLog`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u

theorem stopped_pos_of_cutLog {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgpos : ∀ H, GramFeasible D H → 0 ≤ g H) {K C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ ε, 0 < ε → ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → ε ≤ g H →
      gramGenerator D0 D (fun G => cutH ε (g G)) H ≤ C)
    (h0 : ∀ᵐ ω ∂Q, 0 < g (G 0 ω)) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < g (stoppedProcess G (gramTraceStop G K) t ω) := by
  obtain ⟨E, hE, hgE⟩ := exists_feasible_bound (D := D) hg K
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hnull : ∀ j : ℕ, Q {ω | ((1 / ((j : ℝ) + 2)) ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
      g (stoppedProcess G (gramTraceStop G K) t ω) = 0} = 0 := by
    intro j
    set δ : ℝ := 1 / ((j : ℝ) + 2)
    have hδ : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
    set c0 := max (Real.log E - Real.log δ + C * t) 0
    have hc0 : 0 ≤ c0 := le_max_right _ _
    have hb : ∀ n : ℕ, (Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
        g (stoppedProcess G (gramTraceStop G K) t ω) = 0}).toReal ≤ c0 / ((n : ℝ) + 1) := by
      intro n
      set ε := δ * Real.exp (-((n : ℝ) + 1))
      have hε : 0 < ε := by positivity
      have hεδ : ε < δ := by
        have : Real.exp (-((n : ℝ) + 1)) < 1 := Real.exp_lt_one_iff.2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        nlinarith
      refine (markov_cutLog hD hG hg hε hεδ hδ1 hC hE hgE (hbar ε hε) t).trans ?_
      have hlogε : Real.log ε = Real.log δ - ((n : ℝ) + 1) := by
        rw [Real.log_mul hδ.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
      rw [hlogε]
      exact div_le_div_of_nonneg_left hc0 (by positivity) (by linarith)
    have hz : (Q {ω | (δ ≤ g (G 0 ω) ∧ ((G 0 ω).1.trace).re < K) ∧
        g (stoppedProcess G (gramTraceStop G K) t ω) = 0}).toReal = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun x hx => ?_) ENNReal.toReal_nonneg
      obtain ⟨n, hn⟩ := exists_nat_gt (c0 / x)
      refine (hb n).trans ?_
      rw [zero_add, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hx] at hn
      nlinarith
    exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right (measure_ne_top _ _)
  have hall := ae_all_iff.2 fun j => measure_eq_zero_iff_ae_notMem.1 (hnull j)
  filter_upwards [hall, h0, hG.feasible] with ω hj hpos hfe
  rw [stoppedProcess_eq_stopTime] at hj ⊢
  rcases le_or_gt K ((G 0 ω).1.trace).re with hK | hK
  · have h0' : gramTraceStop G K ω = 0 := le_antisymm (iInf₂_le (0 : ℝ≥0) hK) bot_le
    rw [h0', stopTime_of_eq_zero]; exact hpos
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have hδ : 1 / ((n : ℝ) + 2) ≤ g (G 0 ω) := by
      refine le_trans ?_ hn.le
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hne := hj n
    simp only [not_and] at hne
    exact lt_of_le_of_ne (hgpos _ (hfe _)) (Ne.symm (hne ⟨hδ, hK⟩))

theorem principalMinorSum_near_stopped_pos {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) (K : ℝ)
    (h0 : ∀ᵐ ω ∂Q, 0 < principalMinorSum k (G 0 ω).2) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < principalMinorSum k (stoppedProcess G (gramTraceStop G K) t ω).2 :=
  stopped_pos_of_cutLog (g := fun H => principalMinorSum k H.2) hD hG (contDiff_ek_snd k)
    (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).1)
    (by unfold logNearConst; positivity)
    (fun ε hε H hH hK => (gramGenerator_cutLog_le hD0 hD k K hε hH hK).1) h0 t

theorem principalMinorSum_far_stopped_pos {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) (K : ℝ)
    (h0 : ∀ᵐ ω ∂Q, 0 < principalMinorSum k ((G 0 ω).1 - (G 0 ω).2)) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < principalMinorSum k ((stoppedProcess G (gramTraceStop G K) t ω).1 -
      (stoppedProcess G (gramTraceStop G K) t ω).2) :=
  stopped_pos_of_cutLog (g := fun H => principalMinorSum k (H.1 - H.2)) hD hG
    (contDiff_ek_fst_sub_snd k) (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).2)
    (by unfold logFarConst; positivity)
    (fun ε hε H hH hK => (gramGenerator_cutLog_le hD0 hD k K hε hH hK).2) h0 t

end BlockBand.SourceProcess.Stochastic.GramUniqueness
