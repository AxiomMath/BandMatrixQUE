module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepPath
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LogCutoff
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank loss: pathwise facts for the log barrier

For a `C²` function `g` of the Gram pair (later `e_k(B)` or `e_k(M − B)`), `ε > 0` and the
exit time `τ_ε` of `Y = toGramReal ∘ G` from `{ε < g}` (`lowExit`), along a continuous path:
* `le_g_of_le_lowExit`: `ε ≤ g(G_s)` for `0 < s ≤ τ_ε`;
* `lowExit_attained`: if `g(G_v) ≤ ε` then `τ_ε = s₀ ≤ v` with `g(G_{s₀}) ≤ ε`;
* `exists_feasible_bound`: `g ≤ E` (some `E ≥ 1`) on feasible states with `Re Tr M ≤ K`;
* `cutLog_path_ineq`: the Itô process `X` of `cutH ε ∘ g` stopped at `ρ' = σ_K ∧ τ_ε` satisfies
  `X_{t∧ρ'} ≥ cutH ε (g(G_{t∧ρ'})) − cutH ε (g(G_0)) − C t` when `𝒢(cutH ε ∘ g) ≤ C` (`C ≥ 0`)
  on feasible states with `Re Tr M ≤ K`, `g ≥ ε`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The open set `{ε < g}` in real Gram coordinates. -/
def lowOpen (g : Matrix c c ℂ × Matrix c c ℂ → ℝ) (ε : ℝ) : Set (Fin (gramDim c) → ℝ) :=
  {y | ε < g (fromGramReal y)}

theorem isOpen_lowOpen {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hg : ContDiff ℝ 2 g) (ε : ℝ) :
    IsOpen (lowOpen g ε) :=
  isOpen_lt continuous_const (contDiff_comp_fromGramReal hg).continuous

/-- The exit time `τ_ε` from `{ε < g}`. -/
def lowExit {Ω : Type*} (g : Matrix c c ℂ × Matrix c c ℂ → ℝ) (ε : ℝ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (ω : Ω) : WithTop ℝ≥0 :=
  exitTimeFrom (lowOpen g ε) (fun t ω => toGramReal (G t ω)) ω

theorem le_g_of_le_lowExit {Ω : Type*} {g : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hg : ContDiff ℝ 2 g) {ε : ℝ} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω}
    (hc : Continuous fun t => G t ω) {s : ℝ≥0} (hs0 : 0 < s)
    (hs : (s : WithTop ℝ≥0) ≤ lowExit g ε G ω) : ε ≤ g (G s ω) := by
  have hcont : Continuous fun v => g (G v ω) := hg.continuous.comp hc
  have hS : IsClosed {v : ℝ≥0 | ε ≤ g (G v ω)} := isClosed_le continuous_const hcont
  have hsub : Iio s ⊆ {v : ℝ≥0 | ε ≤ g (G v ω)} := fun v hv => by
    have h := mem_of_lt_exitTimeFrom (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv) hs)
    simp only [lowOpen, mem_ofPred_eq, fromGramReal_toGramReal] at h
    exact h.le
  have hu : s ∈ closure (Iio s) := by
    rw [closure_Iio' (a := s) ⟨0, hs0⟩]; exact le_rfl
  exact closure_minimal hsub hS hu

theorem lowExit_attained {Ω : Type*} {g : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hg : ContDiff ℝ 2 g) {ε : ℝ} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω}
    (hc : Continuous fun t => G t ω) {v : ℝ≥0} (hv : g (G v ω) ≤ ε) :
    ∃ s₀ : ℝ≥0, lowExit g ε G ω = s₀ ∧ s₀ ≤ v ∧ g (G s₀ ω) ≤ ε := by
  have hle : lowExit g ε G ω ≤ v := iInf₂_le v (by
    simp only [lowOpen, mem_ofPred_eq, fromGramReal_toGramReal, not_lt]; exact hv)
  rcases exitTimeFrom_attained (Y := fun t ω => toGramReal (G t ω)) (isOpen_lowOpen hg ε)
    (continuous_toGramReal.comp hc) with h | h
  · have h' : lowExit g ε G ω = ⊤ := h
    rw [h'] at hle; exact absurd hle (not_le.2 (WithTop.coe_lt_top v))
  · obtain ⟨s₀, hs₀, hn⟩ := h
    have hs₀' : lowExit g ε G ω = s₀ := hs₀
    refine ⟨s₀, hs₀', ?_, ?_⟩
    · rw [hs₀'] at hle; exact_mod_cast hle
    · simpa only [lowOpen, mem_ofPred_eq, fromGramReal_toGramReal, not_lt] using hn

theorem exists_feasible_bound {D : Matrix c c ℂ} {g : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hg : ContDiff ℝ 2 g) (K : ℝ) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → g H ≤ E := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin (gramDim c) → ℝ)
    (max K 0)).exists_bound_of_continuousOn (contDiff_comp_fromGramReal hg).continuous.continuousOn
  refine ⟨max B 1, le_max_right _ _, fun H hH hK => ?_⟩
  have hy : toGramReal H ∈ Metric.closedBall (0 : Fin (gramDim c) → ℝ) (max K 0) := by
    rw [mem_closedBall_zero_iff]
    exact (norm_toGramReal_le_of_feasible hH).trans (hK.trans (le_max_left _ _))
  have := hB _ hy
  rw [fromGramReal_toGramReal, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- The pathwise inequality for the stopped log process. -/
theorem cutLog_path_ineq {Ω : Type*} {D0 : ℝ} {D : Matrix c c ℂ}
    {g : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hg : ContDiff ℝ 2 g) {ε C K : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hbar : ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → ε ≤ g H →
      gramGenerator D0 D (fun G => cutH ε (g G)) H ≤ C)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω} (hc : Continuous fun t => G t ω)
    (hfe : ∀ t, GramFeasible D (G t ω)) (t : ℝ≥0) :
    cutH ε (g (G (stopTime (min (gramTraceStop G K ω) (lowExit g ε G ω)) t) ω)) -
        cutH ε (g (G 0 ω)) - C * t ≤
      stoppedProcess (gramItoProc D0 D (fun G => cutH ε (g G)) G)
        (fun ω => min (gramTraceStop G K ω) (lowExit g ε G ω)) t ω := by
  have hf : ContDiff ℝ 2 fun G => cutH ε (g G) := (contDiff_cutH hε).comp hg
  set ρ := min (gramTraceStop G K ω) (lowExit g ε G ω)
  set u := stopTime ρ t
  have hgen : Continuous fun v : ℝ≥0 =>
      gramRealGen D0 D (fun G => cutH ε (g G)) (toGramReal (G v ω)) :=
    (continuous_gramRealGen D0 D hf).comp (continuous_toGramReal.comp hc)
  have h1 : ∫ s in Ioc (0 : ℝ) u,
      gramRealGen D0 D (fun G => cutH ε (g G)) (toGramReal (G s.toNNReal ω)) ≤
      ∫ _s in Ioc (0 : ℝ) u, C := by
    refine setIntegral_mono_on (integrableOn_Ioc_of_continuous hgen u)
      (integrableOn_const (by simp)) measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
    have hsu : (s.toNNReal : WithTop ℝ≥0) ≤ ρ := by
      refine le_trans (WithTop.coe_le_coe.2 ?_) (stopTime_le_self ρ t)
      exact Real.toNNReal_le_iff_le_coe.2 hs.2
    unfold gramRealGen
    rw [mpGenerator_gramReal D0 D hf]
    exact hbar _ (hfe _) (re_trace_le_of_le_stop hc hs0 (hsu.trans (min_le_left _ _)))
      (le_g_of_le_lowExit hg hc hs0 (hsu.trans (min_le_right _ _)))
  have h2 : ∫ _s in Ioc (0 : ℝ) u, C ≤ C * t := by
    rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, sub_zero,
      max_eq_left (NNReal.coe_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (stopTime_le ρ t)) hC
  have e : stoppedProcess (gramItoProc D0 D (fun G => cutH ε (g G)) G)
      (fun ω => min (gramTraceStop G K ω) (lowExit g ε G ω)) t ω =
      cutH ε (g (G u ω)) - cutH ε (g (G 0 ω)) - ∫ s in Ioc (0 : ℝ) u,
        gramRealGen D0 D (fun G => cutH ε (g G)) (toGramReal (G s.toNNReal ω)) := by
    rw [stoppedProcess_eq_stopTime]
    simp only [gramItoProc, fromGramReal_toGramReal]
    rfl
  rw [e]
  linarith

end BlockBand.SourceProcess.Stochastic.GramUniqueness
