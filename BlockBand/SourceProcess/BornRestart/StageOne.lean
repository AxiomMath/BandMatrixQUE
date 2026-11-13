module

public import BlockBand.SourceProcess.BornRestart.Setup

/-!
# Stage one: localized martingales of the restarted process

The born clauses at the trace level `locLevel j k` give `𝓖`-martingale modifications of
`C_e` stopped at `θ_k` and at `a ∧ θ_k` (optional stopping, `θ_k` below the trace stop). Their
difference is bounded on every window `[a, a + u + 1]`, so the restart lemma gives
(`exists_rs_drift`) an `𝓗`-martingale modification of `u ↦ C^H_e(u ∧ (θ_k - a))`, where
`C^H` is the compensated coordinate of the restarted process.
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

/-- The trace level dominating `θ_k`. -/
def locLevel (j : F → GramState c) (k : ℕ) : ℝ := Fintype.card c * (k + jumpBound j) + 1

theorem stopTime_min_coe (θ : WithTop ℝ≥0) (a v : ℝ≥0) :
    stopTime (min (a : WithTop ℝ≥0) θ) (a + v) = stopTime θ a := by
  induction θ with
  | top => rw [min_top_right, stopTime_coe, stopTime_top, min_eq_right le_self_add]
  | coe x =>
    rw [← WithTop.coe_min, stopTime_coe, stopTime_coe,
      min_eq_right ((min_le_left a x).trans le_self_add)]

/-- **Optional stopping below `θ_k`.** -/
theorem exists_mart_locStop
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (k : ℕ)
    {X : ℝ≥0 → Ω → ℂ}
    (hX : ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧
      ∀ t, N t =ᵐ[Q] stoppedProcess X (gramTraceStop G (locLevel j k)) t)
    (hXc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) (hρθ : ∀ ω, ρ ω ≤ locStop j G β k ω) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess X ρ t := by
  obtain ⟨N, hN, hNX⟩ := hX
  refine exists_martingale_restrict_complex hN hNX hXc hρ ?_ (ae_of_all _ fun _ => rfl)
  filter_upwards [hG.continuous] with ω hc
  exact (hρθ ω).trans (locStop_le_traceStop hc k)

omit [IsProbabilityMeasure Q] in
theorem isStoppingTime_locStop'
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G) (k : ℕ) :
    IsStoppingTime 𝓖 (locStop j G β k) :=
  isStoppingTime_locStop hG.adapted hG.jump k

omit [IsProbabilityMeasure Q] in
theorem continuous_bornCompensated_ae
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (e : Fin 2 × c × c) :
    ∀ᵐ ω ∂Q, Continuous fun t =>
      bornCompensated D0 D G (fun t ω => birthSum j (β ω) (t : ℝ)) e t ω := by
  filter_upwards [hG.continuous] with ω hc
  exact continuous_pComp hc e

/-- **Stage one, compensated coordinates.** -/
theorem exists_rs_drift (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (e : Fin 2 × c × c) (k : ℕ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (rsFil hα hβ) Q ∧ ∀ u, N u =ᵐ[Q] fun ω =>
      pComp D0 D j (fun v => rsH α β G v ω) (rsBirth α β ω) e
        (stopTime (locStop j G β k ω - α (β ω)) u) := by
  have ha := measurable_rsTime hα hβ
  have hθ := isStoppingTime_locStop' hG k
  set X := bornCompensated D0 D G (fun t ω => birthSum j (β ω) (t : ℝ)) e
  obtain ⟨M1, hM1, hM1X⟩ := exists_mart_locStop hG k (hG.drift (locLevel j k) e)
    (continuous_bornCompensated_ae hG e) hθ fun _ => le_rfl
  obtain ⟨M2, hM2, hM2X⟩ := exists_mart_locStop hG k (hG.drift (locLevel j k) e)
    (continuous_bornCompensated_ae hG e) ((isStoppingTime_of_zero ha).min hθ)
    fun _ => min_le_right _ _
  obtain ⟨C, hC0, hC⟩ := exists_pComp_stop_bound (D0 := D0) (D := D) (j := j) e k
  obtain ⟨N, hN, hNX⟩ := exists_martingale_restart (ha := ha) (hM1.sub hM2)
    (X := fun t ω => stoppedProcess X (locStop j G β k) t ω -
      stoppedProcess X (fun ω => min ((α (β ω) : ℝ≥0) : WithTop ℝ≥0) (locStop j G β k ω)) t ω)
    (fun t => by
      filter_upwards [hM1X t, hM2X t] with ω h1 h2
      simp only [Pi.sub_apply, h1, h2, X])
    (by
      filter_upwards [continuous_bornCompensated_ae hG e] with ω hc
      exact (hc.comp (continuous_stopTime _)).sub (hc.comp (continuous_stopTime _)))
    (fun u => ⟨C * (2 + u), by
      filter_upwards [hG.continuous] with ω hc v hv
      simp only [stoppedProcess_eq_stopTime, stopTime_min_coe]
      rw [show X = fun t ω => pComp D0 D j (fun t => G t ω) (β ω) e t from rfl]
      simp only
      rw [← pComp_stop_shift hc]
      refine (hC (fun v => G (α (β ω) + v) ω) (fun f => β ω f - α (β ω)) _ v
        (continuous_shift hc _) (fun s hs => ?_)).trans ?_
      · rw [birthSum_shift]
        exact norm_le_of_lt_locStop hc (by exact_mod_cast lt_tsub_iff_left.1 hs)
      · have : (v : ℝ) ≤ u + 1 := by exact_mod_cast hv
        exact mul_le_mul_of_nonneg_left (by linarith) hC0⟩)
  refine ⟨N, hN, fun u => ?_⟩
  filter_upwards [hNX u, hG.continuous] with ω h hc
  rw [h]
  simp only [stoppedProcess_eq_stopTime, stopTime_min_coe]
  rw [rsH_shift hc]
  exact (pComp_stop_shift hc _ _ u e).symm

end BlockBand.SourceProcess.BornRestart
