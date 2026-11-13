module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepIto
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank creation: pathwise inequalities

Along a good path (`GoodPath`: continuous, feasible at all times, `f(G_0) = 0`), with
`F(u) = f(G_{u ∧ σ_K})`:
* `goodPath_bound`: `0 ≤ F(u) ≤ B` for a constant `B` depending only on `f, K`
  (`f(G_{u∧σ}) = f(G_0) = 0` if `u ∧ σ = 0`, otherwise `Re Tr M ≤ K` at `u ∧ σ`);
* `goodPath_ineq`: if `𝒢f ≤ C f` on feasible states with `Re Tr M ≤ K` (`C ≥ 0`), then
  `F(t) ≤ X_{t∧σ} + C ∫_0^t F(s) ds` with `X = gramItoProc`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- A good path for the no-rank-creation argument. -/
def GoodPath {Ω : Type*} (D : Matrix c c ℂ) (f : Matrix c c ℂ × Matrix c c ℂ → ℝ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (ω : Ω) : Prop :=
  (Continuous fun t => G t ω) ∧ (∀ t, GramFeasible D (G t ω)) ∧ f (G 0 ω) = 0

theorem goodPath_bound {D : Matrix c c ℂ} {f : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hpos : ∀ H, GramFeasible D H → 0 ≤ f H) (K : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (ω : Ω),
      GoodPath D f G ω → ∀ u, 0 ≤ f (G (stopTime (gramTraceStop G K ω) u) ω) ∧
        f (G (stopTime (gramTraceStop G K ω) u) ω) ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin (gramDim c) → ℝ) (max K 0)).exists_bound_of_continuousOn
    (contDiff_comp_fromGramReal hf).continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun G ω hω u => ⟨hpos _ (hω.2.1 _), ?_⟩⟩
  set v := stopTime (gramTraceStop G K ω) u
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with h0 | hv
  · rw [← h0, hω.2.2]; exact le_max_right _ _
  have htr := re_trace_le_of_le_stop hω.1 hv (stopTime_le_self _ u)
  have hy : toGramReal (G v ω) ∈ Metric.closedBall (0 : Fin (gramDim c) → ℝ) (max K 0) := by
    rw [mem_closedBall_zero_iff]
    exact (norm_toGramReal_le_of_feasible (hω.2.1 v)).trans (htr.trans (le_max_left _ _))
  have := hB _ hy
  rw [fromGramReal_toGramReal, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

theorem goodPath_ineq {Ω : Type*} {D0 : ℝ} {D : Matrix c c ℂ}
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) {C K : ℝ} (hC : 0 ≤ C)
    (hpos : ∀ H, GramFeasible D H → 0 ≤ f H)
    (hbar : ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → gramGenerator D0 D f H ≤ C * f H)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω} (hω : GoodPath D f G ω) (t : ℝ≥0) :
    f (G (stopTime (gramTraceStop G K ω) t) ω) ≤
      stoppedProcess (gramItoProc D0 D f G) (gramTraceStop G K) t ω +
        C * ∫ s in Ioc (0 : ℝ) t, f (G (stopTime (gramTraceStop G K ω) s.toNNReal) ω) := by
  obtain ⟨hc, hfe, h0⟩ := hω
  set σ := gramTraceStop G K ω
  set u := stopTime σ t
  have hF : Continuous fun v : ℝ≥0 => f (G (stopTime σ v) ω) :=
    hf.continuous.comp (hc.comp (continuous_stopTime σ))
  have hgen : Continuous fun v : ℝ≥0 => gramRealGen D0 D f (toGramReal (G v ω)) :=
    (continuous_gramRealGen D0 D hf).comp (continuous_toGramReal.comp hc)
  have h1 : ∫ s in Ioc (0 : ℝ) u, gramRealGen D0 D f (toGramReal (G s.toNNReal ω)) ≤
      ∫ s in Ioc (0 : ℝ) u, C * f (G (stopTime σ s.toNNReal) ω) := by
    refine setIntegral_mono_on (integrableOn_Ioc_of_continuous hgen u)
      (integrableOn_Ioc_of_continuous (continuous_const.mul hF) u) measurableSet_Ioc
      fun s hs => ?_
    have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
    have hsu : (s.toNNReal : WithTop ℝ≥0) ≤ σ := by
      refine le_trans (WithTop.coe_le_coe.2 ?_) (stopTime_le_self σ t)
      exact Real.toNNReal_le_iff_le_coe.2 hs.2
    rw [SemimartingaleIto.stopTime_eq_of_le hsu]
    unfold gramRealGen
    rw [mpGenerator_gramReal D0 D hf]
    exact hbar _ (hfe _) (re_trace_le_of_le_stop hc hs0 hsu)
  have h2 : ∫ s in Ioc (0 : ℝ) u, f (G (stopTime σ s.toNNReal) ω) ≤
      ∫ s in Ioc (0 : ℝ) t, f (G (stopTime σ s.toNNReal) ω) :=
    setIntegral_mono_set (integrableOn_Ioc_of_continuous hF t)
      (ae_of_all _ fun s => hpos _ (hfe _))
      (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (stopTime_le σ t))).eventuallyLE
  rw [integral_const_mul] at h1
  have e : stoppedProcess (gramItoProc D0 D f G) (gramTraceStop G K) t ω =
      f (G u ω) - f (G 0 ω) - ∫ s in Ioc (0 : ℝ) u,
        gramRealGen D0 D f (toGramReal (G s.toNNReal ω)) := by
    rw [stoppedProcess_eq_stopTime]
    simp only [gramItoProc, fromGramReal_toGramReal]
    rfl
  rw [e, h0]
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
