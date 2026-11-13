module

public import BlockBand.SourceProcess.BornRestart.StageTwo

/-!
# Stage two: the bracket clauses of the restarted process

On `{a ≤ k}` the compensated product of `H` stopped at `θ_k - a` is the stage-one product
martingale minus the cross terms `C_e(a) C^H_{e'} + C_{e'}(a) C^H_e` (`pBr_stop_shift`). The
factors `C_e(a)` are replaced by their `𝓗₀`-measurable, bounded versions
(`exists_rs_cross`). After optional stopping at `σ^H_K ∧ (θ_k - a)`, the dominated limit
`k → ∞` gives the bracket clause (`rs_bracket_clause`).
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

/-- **The cut-off product clause stopped at `θ_k - a`.** -/
theorem exists_rs_bracket_loc (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (e e' : Fin 2 × c × c) (k : ℕ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (rsFil hα hβ) Q ∧ ∀ t, N t =ᵐ[Q]
      stoppedProcess (fun t ω => rsInd α β k ω *
        pBr D0 D j (fun t => rsH α β G t ω) (rsBirth α β ω) e e' t)
        (fun ω => locStop j G β k ω - α (β ω)) t := by
  obtain ⟨Nb, hNb, hNbX⟩ := exists_rs_bracket hα hβ hG e e' k
  obtain ⟨N1, hN1, hN1X⟩ := exists_rs_drift hα hβ hG e k
  obtain ⟨N2, hN2, hN2X⟩ := exists_rs_drift hα hβ hG e' k
  obtain ⟨z1, hz1, ⟨C1, hC1⟩, hz1X⟩ := exists_rs_cross hα hβ hG e k
  obtain ⟨z2, hz2, ⟨C2, hC2⟩, hz2X⟩ := exists_rs_cross hα hβ hG e' k
  refine ⟨fun t ω => Nb t ω - z1 ω * N2 t ω - z2 ω * N1 t ω,
    (hNb.sub (martingale_const_mul hN2 hz1 hC1)).sub (martingale_const_mul hN1 hz2 hC2),
    fun t => ?_⟩
  filter_upwards [hNbX t, hN1X t, hN2X t, hz1X, hz2X, hG.continuous] with ω h1 h2 h3 h4 h5 hc
  rw [stoppedProcess_eq_stopTime, h1, h2, h3, h4, h5, rsH_shift hc,
    show rsBirth α β ω = fun f => β ω f - α (β ω) from rfl, pBr_stop_shift hc]
  ring

/-- **The bracket clauses of the restarted process.** -/
theorem rs_bracket_clause (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (K : ℝ)
    (e e' : Fin 2 × c × c) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (rsFil hα hβ) Q ∧ ∀ t, N t =ᵐ[Q]
      stoppedProcess (fun t ω =>
        bornCompensated D0 D (rsH α β G)
          (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) e t ω *
        bornCompensated D0 D (rsH α β G)
          (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) e' t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (rsH α β G s.toNNReal ω))
        (gramTraceStop (rsH α β G) K) t := by
  set X : ℝ≥0 → Ω → ℂ := fun t ω => pBr D0 D j (fun t => rsH α β G t ω) (rsBirth α β ω) e e' t
  have hgood := hG.continuous.and hG.feasible
  have hstep : ∀ k : ℕ, ∃ Y : ℝ≥0 → Ω → ℂ, Martingale Y (rsFil hα hβ) Q ∧ ∀ t, Y t =ᵐ[Q]
      stoppedProcess (fun t ω => rsInd α β k ω * X t ω) (fun ω =>
        min (gramTraceStop (rsH α β G) K ω) (locStop j G β k ω - α (β ω))) t := fun k => by
    obtain ⟨N, hN, hNX⟩ := exists_rs_bracket_loc hα hβ hG e e' k
    refine exists_martingale_restrict_complex (σ := fun ω => locStop j G β k ω - α (β ω)) hN hNX
      ?_ ((isStoppingTime_rsTrace hα hβ hG K).min (isStoppingTime_rsLoc hα hβ hG k))
      (ae_of_all _ fun _ => min_le_right _ _) ?_
    · filter_upwards [hG.continuous] with ω hc
      exact continuous_const.mul (continuous_pBr (continuous_rsH hc) e e')
    · filter_upwards [hG.continuous] with ω hc
      rw [pieceStop_eq (continuous_rsH hc) K]
  choose Y hY hYX using hstep
  obtain ⟨C, hC0, hC⟩ := exists_pBr_stop_bound (D0 := D0) (D := D) (j := j) e e'
    (K + jumpBound j)
  refine exists_martingale_of_tendsto (Y := Y) (V := stoppedProcess X (gramTraceStop (rsH α β G) K))
    (fun u => @StronglyMeasurable.limUnder ℕ Ω ℂ (rsFil hα hβ u) _ _ atTop _ (fun k => Y k u) _ _
      fun k => (hY k).1 u)
    (fun k u => (((hY k).1 u).mono ((rsFil hα hβ).le u)).aestronglyMeasurable)
    (fun u => ?_) (fun u => ⟨C * (1 + u) ^ 2, fun k => ?_⟩)
    (fun k s t hst B hB => ((hY k).setIntegral_eq hst hB).symm)
  · filter_upwards [ae_all_iff.2 fun k => hYX k u, hG.continuous] with ω h hc
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_rsStop hc u,
      (tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_ge_atTop (α (β ω))] with k hk hk'
    rw [h k, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stopTime_min_of_le hk]
    simp only [rsInd, hk', ↓reduceIte, one_mul]
  · filter_upwards [hYX k u, hgood] with ω h ⟨hc, hf⟩
    rw [h, stoppedProcess_eq_stopTime]
    refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (norm_rsInd_le k ω)).trans ?_)
    refine hC (fun t => rsH α β G t ω) (rsBirth α β ω) _ u (continuous_rsH hc) fun s hs => ?_
    refine norm_le_of_lt_traceStop (D := D) (fun s => ?_) (lt_of_lt_of_le hs (min_le_left _ _))
    rw [rsH_eq hc]
    exact hf _

end BlockBand.SourceProcess.BornRestart
