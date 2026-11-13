module

public import BlockBand.SourceProcess.BornRestart.StageOneBr

/-!
# Stage two: the drift clauses of the restarted process

The trace stop `σ^H_K` of `H` is a.s. the `𝓗`-stopping time `pieceStop` (`𝓗` is
right-continuous). Optional stopping of the stage-one martingales (stopped at
`θ_k - a`) at `σ^H_K ∧ (θ_k - a)` gives martingale modifications of `C^H` stopped there.
These are bounded uniformly in `k` (feasibility before `σ^H_K`) and are eventually equal to
`C^H(u ∧ σ^H_K)`, so the dominated limit `k → ∞` gives the drift clause
(`rs_drift_clause`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c} {α : (F → ℝ) → ℝ≥0} {Ω : Type} {m : MeasurableSpace Ω}
  {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω} [IsProbabilityMeasure Q] {β : Ω → F → ℝ}
  {G : ℝ≥0 → Ω → GramState c}

theorem stopTime_min_of_le {σ θ : WithTop ℝ≥0} {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ θ) :
    stopTime (min σ θ) u = stopTime σ u := by
  unfold stopTime
  congr 1
  rw [← min_assoc, min_eq_left ((min_le_left _ _).trans hu)]

theorem le_sub_of_add_le' {θ : WithTop ℝ≥0} {a u : ℝ≥0} (h : ((a + u : ℝ≥0) : WithTop ℝ≥0) ≤ θ) :
    (u : WithTop ℝ≥0) ≤ θ - a := by
  induction θ with
  | top => rw [WithTop.top_sub_coe]; exact le_top
  | coe x =>
    rw [← WithTop.coe_sub]
    exact WithTop.coe_le_coe.2 (le_tsub_of_add_le_left (WithTop.coe_le_coe.1 h))

omit [DecidableEq c] in
theorem eventually_le_rsStop {ω : Ω}
    (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) (u : ℝ≥0) :
    ∀ᶠ k : ℕ in atTop, (u : WithTop ℝ≥0) ≤ locStop j G β k ω - α (β ω) := by
  filter_upwards [eventually_le_locStop hc (α (β ω) + u)] with k hk
  exact le_sub_of_add_le' hk

omit [IsProbabilityMeasure Q] in
theorem isStoppingTime_rsTrace (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (K : ℝ) :
    IsStoppingTime (rsFil hα hβ) (pieceStop j (rsH α β G) (rsBirth α β) K) :=
  isStoppingTime_pieceStop (stronglyMeasurable_rsH hα hβ hG.adapted)
    (measurable_rsBirth hα hβ) K

omit [IsProbabilityMeasure Q] in
theorem isStoppingTime_rsLoc (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (k : ℕ) :
    IsStoppingTime (rsFil hα hβ) fun ω => locStop j G β k ω - α (β ω) :=
  isStoppingTime_sub_shift (measurable_rsTime hα hβ) (isStoppingTime_locStop' hG k)

/-- **The drift clauses of the restarted process.** -/
theorem rs_drift_clause (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (K : ℝ)
    (e : Fin 2 × c × c) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (rsFil hα hβ) Q ∧ ∀ t, N t =ᵐ[Q]
      stoppedProcess (bornCompensated D0 D (rsH α β G)
        (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) e)
        (gramTraceStop (rsH α β G) K) t := by
  set X := bornCompensated D0 D (rsH α β G)
    (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) e
  have hgood := hG.continuous.and hG.feasible
  have hXc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω := by
    filter_upwards [hG.continuous] with ω hc
    exact continuous_pComp (continuous_rsH hc) e
  have hstep : ∀ k : ℕ, ∃ Y : ℝ≥0 → Ω → ℂ, Martingale Y (rsFil hα hβ) Q ∧ ∀ t, Y t =ᵐ[Q]
      stoppedProcess X (fun ω => min (gramTraceStop (rsH α β G) K ω)
        (locStop j G β k ω - α (β ω))) t := fun k => by
    obtain ⟨N, hN, hNX⟩ := exists_rs_drift hα hβ hG e k
    refine exists_martingale_restrict_complex (σ := fun ω => locStop j G β k ω - α (β ω)) hN
      (fun t => by
        filter_upwards [hNX t] with ω h
        rw [h]; rfl) hXc ((isStoppingTime_rsTrace hα hβ hG K).min (isStoppingTime_rsLoc hα hβ hG k))
      (ae_of_all _ fun _ => min_le_right _ _) ?_
    filter_upwards [hG.continuous] with ω hc
    rw [pieceStop_eq (continuous_rsH hc) K]
  choose Y hY hYX using hstep
  obtain ⟨C, hC0, hC⟩ := exists_pComp_stop_bound (D0 := D0) (D := D) (j := j) e (K + jumpBound j)
  refine exists_martingale_of_tendsto (Y := Y)
    (fun u => @StronglyMeasurable.limUnder ℕ Ω ℂ (rsFil hα hβ u) _ _ atTop _ (fun k => Y k u) _ _
      fun k => (hY k).1 u)
    (fun k u => (((hY k).1 u).mono ((rsFil hα hβ).le u)).aestronglyMeasurable)
    (fun u => ?_) (fun u => ⟨C * (1 + u), fun k => ?_⟩)
    (fun k s t hst B hB => ((hY k).setIntegral_eq hst hB).symm)
  · filter_upwards [ae_all_iff.2 fun k => hYX k u, hG.continuous] with ω h hc
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_rsStop hc u] with k hk
    rw [h k, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stopTime_min_of_le hk]
  · filter_upwards [hYX k u, hgood] with ω h ⟨hc, hf⟩
    rw [h, stoppedProcess_eq_stopTime]
    refine hC (fun t => rsH α β G t ω) (rsBirth α β ω) _ u (continuous_rsH hc) fun s hs => ?_
    refine norm_le_of_lt_traceStop (D := D) (fun s => ?_) (lt_of_lt_of_le hs (min_le_left _ _))
    rw [rsH_eq hc]
    exact hf _

end BlockBand.SourceProcess.BornRestart
