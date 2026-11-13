module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepBounds
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ItoUniverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank creation: Itô's formula for `f(G)` stopped at the trace stop

For a feasible Gram martingale-problem solution `G` (any universe), a `C²` function `f` of the
Gram pair and a trace level `K`, the process
`X_t = f(G_t) − f(G_0) − ∫_0^t 𝓛φ(Y_s) ds` (`gramItoProc`; `Y = toGramReal ∘ G`,
`φ = f ∘ fromGramReal`, `𝓛φ(toGramReal H) = gramGenerator f H`) stopped at `σ_K` has a martingale
modification (`exists_martingale_gramItoProc`), hence `E X_{t∧σ_K} = 0`
(`integral_gramItoProc_stopped`).

Proof: the real-coordinate martingale problem (`isMPSolutionOn_gramReal`), the Itô formula for
martingale-problem solutions in every universe (`martingaleProblemItoU_holds`)
on the ball `B(0, max K 0 + 1)`, which contains every feasible state with `Re Tr M < K`
(`norm_toGramReal_le_of_feasible`), then optional stopping at the raw hitting time of
`{K ≤ Re Tr M}`, equal a.s. to `σ_K` (`exists_martingale_restrict`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The real generator `𝓛φ` of `φ = f ∘ fromGramReal`. -/
def gramRealGen (D0 : ℝ) (D : Matrix c c ℂ) (f : Matrix c c ℂ × Matrix c c ℂ → ℝ)
    (y : Fin (gramDim c) → ℝ) : ℝ :=
  mpGenerator (gramRealDrift D0 D) (gramRealCov D0 D) (fun y => f (fromGramReal y)) y

/-- The Itô process of `f(G)`. -/
def gramItoProc {Ω : Type*} (D0 : ℝ) (D : Matrix c c ℂ) (f : Matrix c c ℂ × Matrix c c ℂ → ℝ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (fromGramReal (toGramReal (G t ω))) - f (fromGramReal (toGramReal (G 0 ω))) -
    ∫ s in Ioc (0 : ℝ) t, gramRealGen D0 D f (toGramReal (G s.toNNReal ω))

theorem contDiff_comp_fromGramReal {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 fun y : Fin (gramDim c) → ℝ => f (fromGramReal y) :=
  hf.comp fromGramReal.contDiff

theorem continuous_gramRealGen (D0 : ℝ) (D : Matrix c c ℂ) {f : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (gramRealGen D0 D f) := by
  have hφ := contDiff_comp_fromGramReal hf
  have h1 : Continuous (fderiv ℝ fun y : Fin (gramDim c) → ℝ => f (fromGramReal y)) :=
    hφ.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ fun y : Fin (gramDim c) → ℝ => f (fromGramReal y))) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  unfold gramRealGen mpGenerator
  refine (continuous_finsetSum _ fun i _ => ?_).add (continuous_const.mul
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_))
  · exact ((continuous_apply i).comp (continuous_gramRealDrift D0 D)).mul
      (h1.clm_apply continuous_const)
  · exact ((continuous_gramRealCov D0 D).matrix_elem i j).mul
      ((h2.clm_apply continuous_const).clm_apply continuous_const)

theorem continuous_gramItoProc {Ω : Type*} (D0 : ℝ) (D : Matrix c c ℂ)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω} (hc : Continuous fun t => G t ω) :
    Continuous fun t => gramItoProc D0 D f G t ω := by
  have hφ := (contDiff_comp_fromGramReal hf).continuous
  have hp : Continuous fun u => gramRealGen D0 D f (toGramReal (G u ω)) :=
    (continuous_gramRealGen D0 D hf).comp (continuous_toGramReal.comp hc)
  exact ((hφ.comp (continuous_toGramReal.comp hc)).sub continuous_const).sub
    (continuous_setIntegral_Ioc (g := fun u => gramRealGen D0 D f (toGramReal (G u ω)))
      fun t => integrableOn_Ioc_of_continuous hp t)

/-- The trace super-level set in real coordinates. -/
def traceSuperLevel (K : ℝ) : Set (Fin (gramDim c) → ℝ) :=
  {y | K ≤ ((fromGramReal y).1.trace).re}

theorem isClosed_traceSuperLevel (K : ℝ) : IsClosed (traceSuperLevel (c := c) K) :=
  isClosed_le continuous_const (Complex.continuous_re.comp
    ((continuous_fst.comp continuous_fromGramReal').matrix_trace))

theorem hitTime_traceSuperLevel {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (K : ℝ) (ω : Ω) :
    hitTime (traceSuperLevel K) (fun t ω => toGramReal (G t ω)) ω = gramTraceStop G K ω := by
  simp only [hitTime, gramTraceStop, traceSuperLevel, mem_ofPred_eq, fromGramReal_toGramReal]

universe u

/-- **Itô for `f(G)` stopped at the trace stop.** -/
theorem exists_martingale_gramItoProc {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) (K : ℝ) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧
      ∀ t, N t =ᵐ[Q] stoppedProcess (gramItoProc D0 D f G) (gramTraceStop G K) t := by
  have hY := isMPSolutionOn_gramReal hD hG
  have hYm : ∀ t, Measurable[𝓖 t] (fun ω => toGramReal (G t ω)) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted t)).measurable
  set R : ℝ := max K 0 + 1
  have hW : IsInteriorDomain (Metric.ball (0 : Fin (gramDim c) → ℝ) R) univ :=
    ⟨Metric.isOpen_ball, (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall, subset_univ _⟩
  obtain ⟨M, hM, hMX⟩ := martingaleProblemItoU_holds.{u} _ Ω Q 𝓖 _ _ univ isOpen_univ
    (continuous_gramRealDrift D0 D).continuousOn (continuous_gramRealCov D0 D).continuousOn _ hY
    _ (contDiff_comp_fromGramReal hf).contDiffOn _ hW
  refine exists_martingale_restrict (X := gramItoProc D0 D f G) ⟨M, hM, hMX⟩ ?_
    (isStoppingTime_rawHit (F := traceSuperLevel K) hYm) ?_ ?_
  · filter_upwards [hG.continuous] with ω hc
    exact continuous_gramItoProc D0 D hf hc
  · filter_upwards [hG.continuous, hG.feasible] with ω hc hfe
    rw [rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω)) (isClosed_traceSuperLevel K)
      (continuous_toGramReal.comp hc)]
    refine le_iInf₂ fun t ht => iInf₂_le t ?_
    show K ≤ ((fromGramReal (toGramReal (G t ω))).1.trace).re
    rw [fromGramReal_toGramReal]
    by_contra hlt
    push Not at hlt
    refine ht (mem_ball_zero_iff.2 ?_)
    calc ‖toGramReal (G t ω)‖ ≤ ((G t ω).1.trace).re := norm_toGramReal_le_of_feasible (hfe t)
      _ < R := by have := le_max_left K 0; linarith
  · filter_upwards [hG.continuous] with ω hc
    rw [rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω)) (isClosed_traceSuperLevel K)
      (continuous_toGramReal.comp hc), hitTime_traceSuperLevel]

/-- `E X_{t ∧ σ_K} = 0`, with `X_{t∧σ_K}` integrable. -/
theorem integral_gramItoProc_stopped {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) (K : ℝ) (t : ℝ≥0) :
    Integrable (stoppedProcess (gramItoProc D0 D f G) (gramTraceStop G K) t) Q ∧
      ∫ ω, stoppedProcess (gramItoProc D0 D f G) (gramTraceStop G K) t ω ∂Q = 0 := by
  obtain ⟨N, hN, hNX⟩ := exists_martingale_gramItoProc hD hG hf K
  refine ⟨(hN.integrable t).congr (hNX t), ?_⟩
  rw [← integral_congr_ae (hNX t)]
  have h := hN.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae (hNX 0)]
  refine integral_eq_zero_of_ae (ae_of_all _ fun ω => ?_)
  simp [stoppedProcess_eq_stopTime, stopTime_zero, gramItoProc]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
