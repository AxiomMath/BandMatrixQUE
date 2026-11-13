module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepBounds
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Step 9 bridge, part 5: domination before the trace stop

`gram_stopped_bound`: along a continuous path of feasible Gram states, the real compensated
coordinates and compensated products stopped at `σ_K` are bounded on `[0, t]` by a constant
depending only on `D₀, 𝖣, K, t` (states before `σ_K` have `Re Tr M ≤ K`, hence real coordinates
`≤ max K 0`; if `σ_K = 0` the stopped values vanish).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The compensated real product of coordinates `i, j`. -/
def mpBracketProc {Ω : Type*} (D0 : ℝ) (D : Matrix c c ℂ)
    (Y : ℝ≥0 → Ω → Fin (gramDim c) → ℝ) (i j : Fin (gramDim c)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  mpCompensated (gramRealDrift D0 D) Y i t ω * mpCompensated (gramRealDrift D0 D) Y j t ω -
    ∫ s in Ioc (0 : ℝ) t, gramRealCov D0 D (Y s.toNNReal ω) i j

theorem gram_stopped_bound (Ω : Type*) (D0 : ℝ) (D : Matrix c c ℂ) (K : ℝ) (t : ℝ≥0)
    (i j : Fin (gramDim c)) : ∃ C, ∀ (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (ω : Ω),
      (Continuous fun t => G t ω) → (∀ s, GramFeasible D (G s ω)) → ∀ s ≤ t,
      |stoppedProcess (mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i)
          (gramTraceStop G K) s ω| ≤ C ∧
      |stoppedProcess (mpBracketProc D0 D (fun t ω => toGramReal (G t ω)) i j)
          (gramTraceStop G K) s ω| ≤ C := by
  set R := max K 0
  have hcb : IsCompact (Metric.closedBall (0 : Fin (gramDim c) → ℝ) R) := isCompact_closedBall 0 R
  obtain ⟨Cb, hCb⟩ := hcb.exists_bound_of_continuousOn
    ((continuous_apply i).comp (continuous_gramRealDrift D0 D)).continuousOn
  obtain ⟨Cb', hCb'⟩ := hcb.exists_bound_of_continuousOn
    ((continuous_apply j).comp (continuous_gramRealDrift D0 D)).continuousOn
  obtain ⟨Ca, hCa⟩ := hcb.exists_bound_of_continuousOn
    ((continuous_gramRealCov D0 D).matrix_elem i j).continuousOn
  set B := max Cb Cb'
  set C1 := 2 * R + t * B
  refine ⟨C1 ^ 2 + t * |Ca| + |C1|, fun G ω hc hfe s hst => ?_⟩
  set σ := gramTraceStop G K ω
  set u := stopTime σ s
  have hR0 : 0 ≤ R := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans ((norm_nonneg _).trans (hCb 0 (Metric.mem_closedBall_self hR0)))
    (le_max_left _ _)
  have hut : (u : ℝ) ≤ t := NNReal.coe_le_coe.2 ((stopTime_le σ s).trans hst)
  rcases eq_or_ne σ 0 with h0 | h0
  · have hu : u = 0 := by simp only [u, h0, stopTime_of_eq_zero]
    have e1 : ∀ k, mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) k 0 ω = 0 :=
      fun k => by simp [mpCompensated]
    have e2 : mpBracketProc D0 D (fun t ω => toGramReal (G t ω)) i j 0 ω = 0 := by
      rw [mpBracketProc, e1, e1]; simp
    rw [stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
    change |mpCompensated _ _ i u ω| ≤ _ ∧ |mpBracketProc D0 D _ i j u ω| ≤ _
    rw [hu, e1, e2, abs_zero]
    exact ⟨by positivity, by positivity⟩
  have hK0 : ((G 0 ω).1.trace).re < K := by
    by_contra h; push Not at h
    exact h0 (le_antisymm (iInf₂_le (0 : ℝ≥0) h) bot_le)
  have hY : ∀ v ≤ u, ‖toGramReal (G v ω)‖ ≤ R := fun v hv => by
    refine (norm_toGramReal_le_of_feasible (hfe v)).trans (le_trans ?_ (le_max_left _ _))
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with hv0 | hv0
    · rw [← hv0]; exact hK0.le
    · exact re_trace_le_of_le_stop hc hv0 ((WithTop.coe_le_coe.2 hv).trans (stopTime_le_self σ s))
  have hm : ∀ k : Fin (gramDim c), (∀ y ∈ Metric.closedBall (0 : Fin (gramDim c) → ℝ) R,
      ‖gramRealDrift D0 D y k‖ ≤ B) →
      |mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) k u ω| ≤ C1 := by
    intro k hk
    have hint : ‖∫ r in Ioc (0 : ℝ) u, gramRealDrift D0 D (toGramReal (G r.toNNReal ω)) k‖ ≤
        B * volume.real (Ioc (0 : ℝ) u) := norm_setIntegral_le_of_norm_le_const (by simp)
      fun r hr => hk _ (mem_closedBall_zero_iff.2 (hY _ (Real.toNNReal_le_iff_le_coe.2 hr.2)))
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg _)] at hint
    have h1 := (norm_le_pi_norm (toGramReal (G u ω)) k).trans (hY u le_rfl)
    have h2 := (norm_le_pi_norm (toGramReal (G 0 ω)) k).trans (hY 0 (zero_le))
    rw [Real.norm_eq_abs] at h1 h2 hint
    simp only [mpCompensated]
    have := mul_le_mul_of_nonneg_left hut hB0
    have t1 := abs_sub (toGramReal (G u ω) k - toGramReal (G 0 ω) k)
      (∫ r in Ioc (0 : ℝ) u, gramRealDrift D0 D (toGramReal (G r.toNNReal ω)) k)
    have t2 := abs_sub (toGramReal (G u ω) k) (toGramReal (G 0 ω) k)
    simp only [C1]
    linarith
  have hmi := hm i fun y hy => by
    have := hCb y hy; simp only [Function.comp_apply] at this; exact this.trans (le_max_left _ _)
  have hmj := hm j fun y hy => by
    have := hCb' y hy; simp only [Function.comp_apply] at this; exact this.trans (le_max_right _ _)
  have hint : ‖∫ r in Ioc (0 : ℝ) u, gramRealCov D0 D (toGramReal (G r.toNNReal ω)) i j‖ ≤
      |Ca| * volume.real (Ioc (0 : ℝ) u) := norm_setIntegral_le_of_norm_le_const (by simp)
    fun r hr => by
      have := hCa _ (mem_closedBall_zero_iff.2 (hY _ (Real.toNNReal_le_iff_le_coe.2 hr.2)))
      exact this.trans (le_abs_self _)
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg _), Real.norm_eq_abs] at hint
  rw [stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
  change |mpCompensated _ _ i u ω| ≤ _ ∧ |mpBracketProc D0 D _ i j u ω| ≤ _
  have hC1 : 0 ≤ C1 := (abs_nonneg _).trans hmi
  have hta : 0 ≤ (t : ℝ) * |Ca| := mul_nonneg (NNReal.coe_nonneg t) (abs_nonneg Ca)
  have hfirst : C1 ≤ C1 ^ 2 + t * |Ca| + |C1| := by
    nlinarith [abs_nonneg C1, le_abs_self C1, sq_nonneg C1]
  refine ⟨hmi.trans hfirst, ?_⟩
  unfold mpBracketProc
  have t1 := abs_sub (mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i u ω *
    mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) j u ω)
    (∫ r in Ioc (0 : ℝ) u, gramRealCov D0 D (toGramReal (G r.toNNReal ω)) i j)
  rw [abs_mul] at t1
  have t2 := mul_le_mul hmi hmj (abs_nonneg _) hC1
  have t3 := mul_le_mul_of_nonneg_left hut (abs_nonneg Ca)
  nlinarith [abs_nonneg C1, le_abs_self C1]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
