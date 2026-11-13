module
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Exit
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bridge: martingale-problem solutions on `ℝ^d` are continuous semimartingales

Setting: filtered probability space `(Ω, 𝓖, Q)` with a raw filtration (no usual conditions);
`IsMPSolutionOn Q 𝓖 b a Set.univ Y` with continuous coefficients `b : ℝ^d → ℝ^d`,
`a : ℝ^d → ℝ^{d×d}`.

* `IsMPSolutionOn.isContinuousSemimartingale`: a progressive solution is a continuous
  semimartingale with characteristics `(b(Y), a(Y))`;
* `IsMPSolutionOn.isContinuousSemimartingale_of_forall_continuous`: the same when every path
  is continuous (progressive measurability is then automatic).

Why progressive measurability is assumed: `IsMPSolutionOn` only records adaptedness and a.s.
continuity; on the exceptional null set the joint map `(s, ω) ↦ Y_s(ω)` need not be measurable
for the raw (uncompleted) filtration, while `IsContinuousSemimartingale` requires
`IsStronglyProgressive`.
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ}

/-- Exit times from the balls `ball 0 n` tend to `⊤` along a continuous path. -/
theorem tendsto_exitTimeFrom_ball {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hY : Continuous fun t => Y t ω) :
    Tendsto (fun n : ℕ => exitTimeFrom (ball (0 : Fin d → ℝ) n) Y ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).exists_bound_of_continuousOn
    hY.continuousOn
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hlt : (T : WithTop ℝ≥0) < ((T + 1 : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.2 (lt_add_one T)
  refine hlt.trans_le (le_iInf₂ fun t ht => ?_)
  by_contra hcon
  push Not at hcon
  have hb := hC t ⟨zero_le, (WithTop.coe_lt_coe.1 hcon).le⟩
  refine ht (mem_ball_zero_iff.2 (hb.trans_lt (hn₀.trans_le ?_)))
  exact_mod_cast hn

/-- Balls are relatively compact subdomains of `ℝ^d`. -/
theorem isInteriorDomain_ball_univ (r : ℝ) :
    IsInteriorDomain (ball (0 : Fin d → ℝ) r) univ :=
  ⟨isOpen_ball, (isCompact_closedBall 0 r).closure_of_subset ball_subset_closedBall,
    subset_univ _⟩

/-- On continuous paths the raw hitting time of `(ball 0 r)ᶜ` is the exit time from the ball. -/
theorem rawHit_compl_ball_eq {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hY : Continuous fun t => Y t ω)
    (r : ℝ) : rawHit (ball (0 : Fin d → ℝ) r)ᶜ Y ω = exitTimeFrom (ball (0 : Fin d → ℝ) r) Y ω :=
  rawHit_eq_hitTime isOpen_ball.isClosed_compl hY

end BlockBand.SourceProcess.Stochastic.Bridges

namespace BlockBand.SourceProcess.Stochastic.IsMPSolutionOn
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Bridge MP ⇒ semimartingale.** A progressive solution of the `(b, a)` martingale problem
in `ℝ^d` with continuous coefficients is a continuous semimartingale with characteristics
`(b(Y), a(Y))`; the localizing sequence is `rawHit (ball 0 n)ᶜ Y`. -/
theorem isContinuousSemimartingale {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} (hb : Continuous b) (ha : Continuous a)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : IsMPSolutionOn Q 𝓖 b a univ Y)
    (hprog : IsStronglyProgressive 𝓖 Y) :
    IsContinuousSemimartingale Q 𝓖 Y (fun t ω => b (Y t ω)) (fun t ω => a (Y t ω)) := by
  have hmeas : ∀ t, Measurable[𝓖 t] (Y t) := fun t => (hY.adapted t).measurable
  have hst : ∀ (n : ℕ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0),
      stoppedProcess X (exitTimeFrom (ball (0 : Fin d → ℝ) n) Y) t =ᵐ[Q]
        stoppedProcess X (rawHit (ball (0 : Fin d → ℝ) n)ᶜ Y) t := fun n X t => by
    filter_upwards [hY.continuous] with ω hω
    simp only [stoppedProcess_eq_stopTime, rawHit_compl_ball_eq hω]
  refine ⟨hY.adapted, hprog, hY.continuous, fun t => hb.comp_stronglyMeasurable (hprog t),
    fun t => ha.comp_stronglyMeasurable (hprog t), ?_,
    ⟨fun n => rawHit (ball (0 : Fin d → ℝ) n)ᶜ Y, fun n => isStoppingTime_rawHit hmeas, ?_,
      fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [hY.continuous] with ω hω t
    have hc : Continuous fun s : ℝ => Y s.toNNReal ω := hω.comp continuous_real_toNNReal
    exact ⟨fun i => (((continuous_apply i).comp (hb.comp hc)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self, fun i j => ((((continuous_apply j).comp (continuous_apply i)).comp
        (ha.comp hc)).integrableOn_Icc).mono_set Ioc_subset_Icc_self⟩
  · filter_upwards [hY.continuous] with ω hω
    exact (tendsto_exitTimeFrom_ball hω).congr fun n => (rawHit_compl_ball_eq hω _).symm
  · obtain ⟨N, hN, hNe⟩ := hY.drift _ (isInteriorDomain_ball_univ n) i
    exact ⟨N, hN, fun t => (hNe t).trans (hst n _ t)⟩
  · obtain ⟨N, hN, hNe⟩ := hY.bracket _ (isInteriorDomain_ball_univ n) i j
    exact ⟨N, hN, fun t => (hNe t).trans (hst n _ t)⟩

/-- **Bridge MP ⇒ semimartingale, every path continuous.** -/
theorem isContinuousSemimartingale_of_forall_continuous
    {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hb : Continuous b) (ha : Continuous a) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : IsMPSolutionOn Q 𝓖 b a univ Y) (hc : ∀ ω, Continuous fun t => Y t ω) :
    IsContinuousSemimartingale Q 𝓖 Y (fun t ω => b (Y t ω)) (fun t ω => a (Y t ω)) :=
  hY.isContinuousSemimartingale hb ha
    (StronglyAdapted.isStronglyProgressive_of_continuous hY.adapted hc)

end BlockBand.SourceProcess.Stochastic.IsMPSolutionOn
