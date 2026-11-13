module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealPath
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A Gram martingale-problem solution solves the real-coordinate martingale problem

`isMPSolutionOn_gramReal`: if `G` is a (feasible) solution of the Gram martingale problem
(`IsGramMartingaleSolution`) and `𝖣` is a signature, then its real
coordinates `Y = toGramReal ∘ G` solve the `(gramRealDrift, gramRealCov)` martingale problem
in `ℝ^{4|c|²}` (`IsMPSolutionOn … univ`). Hence the Itô formula for martingale-problem solutions
(`martingaleProblemIto_holds`) applies to `Y`, with generator `gramGenerator`
(`mpGenerator_gramReal`).

Proof. For a relatively compact `W`, `W ⊆ {Re Tr M < K}` for `K = |c| R + 1` (`W ⊆ B(0,R)`),
so the raw hitting time `ρ = rawHit Wᶜ Y` (a stopping time, equal to the exit time on continuous
paths) satisfies `ρ ≤ σ_K` a.s. The real compensated coordinates are `Re`/`Im` of the complex
ones; the real compensated products are `L(N_e N_e' − ∫Γ) + L'(N_e N̄_e' − ∫Γ')` with
`N̄_e' = N_{e'ᵀ}` (Hermitian symmetry along feasible paths). Their `σ_K`-stopped versions have
martingale modifications by the Gram clauses, and optional stopping at `ρ ≤ σ_K` gives the
`IsMPSolutionOn` clauses (`exists_martingale_restrict`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The complex coordinate and real part of the real index `i`. -/
abbrev qi (i : Fin (gramDim c)) : gramRealIdx c := (gramRealEquiv c).symm i

omit [DecidableEq c] in
theorem toGramReal_apply (G : Matrix c c ℂ × Matrix c c ℂ) (i : Fin (gramDim c)) :
    toGramReal G i = reIm (qi i).2 (gramEntry (qi i).1 G) := rfl

omit [DecidableEq c] in
theorem re_trace_le (G : Matrix c c ℂ × Matrix c c ℂ) {R : ℝ} (h : ‖toGramReal G‖ ≤ R) :
    (G.1.trace).re ≤ Fintype.card c * R := by
  have hi : ∀ i, (G.1 i i).re ≤ R := fun i => by
    have e : (G.1 i i).re = toGramReal G (gramRealEquiv c ((0, i, i), 0)) := by
      simp [toGramReal_apply, reIm, gramEntry]
    rw [e]
    exact (le_abs_self _).trans ((norm_le_pi_norm (toGramReal G) _).trans h)
  calc (G.1.trace).re = ∑ i, (G.1 i i).re := by simp [Matrix.trace, Complex.re_sum]
    _ ≤ ∑ _i : c, R := Finset.sum_le_sum fun i _ => hi i
    _ = Fintype.card c * R := by simp

omit [DecidableEq c] in
/-- A relatively compact domain lies below a trace level. -/
theorem exists_trace_level {W : Set (Fin (gramDim c) → ℝ)} (hW : IsInteriorDomain W univ) :
    ∃ K : ℝ, ∀ H : Matrix c c ℂ × Matrix c c ℂ, toGramReal H ∈ W → (H.1.trace).re < K := by
  obtain ⟨R, hR⟩ := hW.2.1.isBounded.subset_closedBall 0
  refine ⟨Fintype.card c * R + 1, fun H hH => ?_⟩
  have h := hR (subset_closure hH)
  rw [Metric.mem_closedBall, dist_zero_right] at h
  linarith [re_trace_le H h]

omit [DecidableEq c] in
theorem hitTime_le_gramTraceStop {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    {W : Set (Fin (gramDim c) → ℝ)} {K : ℝ}
    (hK : ∀ H : Matrix c c ℂ × Matrix c c ℂ, toGramReal H ∈ W → (H.1.trace).re < K) (ω : Ω) :
    hitTime Wᶜ (fun t ω => toGramReal (G t ω)) ω ≤ gramTraceStop G K ω := by
  unfold hitTime gramTraceStop
  refine le_iInf₂ fun t ht => iInf₂_le t fun hW => ?_
  exact absurd ht (not_le.mpr (hK _ hW))

section Path
variable {Ω : Type*} {D0 : ℝ} {D : Matrix c c ℂ} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
  {ω : Ω}

theorem gramRealDrift_apply (H : Matrix c c ℂ × Matrix c c ℂ) (i : Fin (gramDim c)) :
    gramRealDrift D0 D (toGramReal H) i = reImCLM (qi i).2 (gramDriftEntry D0 D (qi i).1 H) := by
  rw [gramRealDrift, fromGramReal_toGramReal, toGramReal_apply, gramEntry_gramDriftG,
    reImCLM_apply]

theorem mpCompensated_gramReal (hc : Continuous fun t => G t ω) (i : Fin (gramDim c))
    (t : ℝ≥0) :
    mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i t ω =
      reImCLM (qi i).2 (gramCompensated D0 D G (qi i).1 t ω) := by
  have hint : Integrable (fun s : ℝ => gramDriftEntry D0 D (qi i).1 (G s.toNNReal ω))
      (volume.restrict (Ioc 0 t)) :=
    integrableOn_Ioc_of_continuous ((continuous_gramDriftEntry D0 D _).comp hc) t
  simp only [mpCompensated, gramCompensated, gramRealDrift_apply]
  rw [ContinuousLinearMap.integral_comp_comm _ hint, map_sub, map_sub, toGramReal_apply,
    toGramReal_apply]
  simp only [reImCLM_apply]

theorem continuous_gramRealDrift_path (hc : Continuous fun t => G t ω) (i : Fin (gramDim c)) :
    Continuous fun u : ℝ≥0 => gramRealDrift D0 D (toGramReal (G u ω)) i := by
  simp only [gramRealDrift_apply]
  exact (reImCLM _).continuous.comp ((continuous_gramDriftEntry D0 D _).comp hc)

theorem continuous_mpCompensated_gramReal (hc : Continuous fun t => G t ω)
    (i : Fin (gramDim c)) :
    Continuous fun t => mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i t ω :=
  ((((continuous_apply i).comp (continuous_toGramReal.comp hc)).sub continuous_const).sub
    (continuous_setIntegral_Ioc (g := fun u => gramRealDrift D0 D (toGramReal (G u ω)) i) fun t =>
      integrableOn_Ioc_of_continuous (continuous_gramRealDrift_path hc i) t))

omit [DecidableEq c] in
theorem star_gramCompensated (hD : Dᴴ = D)
    (hf : ∀ s, (G s ω).1ᴴ = (G s ω).1 ∧ (G s ω).2ᴴ = (G s ω).2) (e : Fin 2 × c × c) (t : ℝ≥0) :
    star (gramCompensated D0 D G e t ω) = gramCompensated D0 D G (gramSwap e) t ω := by
  unfold gramCompensated
  rw [star_sub, star_sub, star_gramEntry_of_herm (hf t).1 (hf t).2,
    star_gramEntry_of_herm (hf 0).1 (hf 0).2]
  congr 1
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext s
  rw [← Complex.star_def, star_gramDriftEntry hD (hf _).1 (hf _).2]

end Path

end BlockBand.SourceProcess.Stochastic.GramUniqueness
