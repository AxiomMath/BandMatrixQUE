module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankNoCreation
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank creation, almost surely for all times and trace levels

`ae_forall_stopped_eq_zero`: if `f` is continuous and `f(G_{t∧σ_K}) = 0` a.s. for each `t` and
`K`, then a.s. it holds for all `t` and `K` simultaneously. Zero is a closed condition: take
rational `t` and natural `K = n`, use path continuity in `t` and `G_{t∧σ_K} = G_{t'∧σ_n}` with
`t' = t ∧ σ_K` for `K ≤ n` (`gramTraceStop` is monotone in `K`).
`principalMinorSum_{near,far}_ae_forall_eq_zero`: rank creation is excluded a.s. for all `t, K`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

omit [DecidableEq c] in
theorem gramTraceStop_mono {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) {K K' : ℝ}
    (h : K ≤ K') (ω : Ω) : gramTraceStop G K ω ≤ gramTraceStop G K' ω :=
  le_iInf₂ fun t ht => iInf₂_le t (h.trans ht)

omit [DecidableEq c] in
/-- `G_{t∧σ_K} = G_{t'∧σ_{K'}}` with `t' = t ∧ σ_K`, for `K ≤ K'`. -/
theorem stopped_eq_restop {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) {K K' : ℝ}
    (h : K ≤ K') (t : ℝ≥0) (ω : Ω) :
    stoppedProcess G (gramTraceStop G K) t ω =
      stoppedProcess G (gramTraceStop G K') (stopTime (gramTraceStop G K ω) t) ω := by
  simp only [stoppedProcess_eq_stopTime]
  rw [SemimartingaleIto.stopTime_eq_of_le ((stopTime_le_self _ t).trans (gramTraceStop_mono G h ω))]

omit [DecidableEq c] in
theorem ae_forall_stopped_eq_zero {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hc : ∀ᵐ ω ∂Q, Continuous fun t => G t ω)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : Continuous f)
    (h : ∀ (t : ℝ≥0) (K : ℝ), ∀ᵐ ω ∂Q, f (stoppedProcess G (gramTraceStop G K) t ω) = 0) :
    ∀ᵐ ω ∂Q, ∀ (t : ℝ≥0) (K : ℝ), f (stoppedProcess G (gramTraceStop G K) t ω) = 0 := by
  have hq : ∀ᵐ ω ∂Q, ∀ (q : ℚ) (n : ℕ),
      f (stoppedProcess G (gramTraceStop G n) (q : ℝ).toNNReal ω) = 0 :=
    ae_all_iff.2 fun q => ae_all_iff.2 fun n => h _ _
  filter_upwards [hq, hc] with ω hω hcω t K
  obtain ⟨n, hn⟩ := exists_nat_ge K
  rw [stopped_eq_restop G hn t ω]
  have hcont : Continuous fun r : ℝ =>
      f (stoppedProcess G (gramTraceStop G n) r.toNNReal ω) := by
    simp only [stoppedProcess_eq_stopTime]
    exact hf.comp ((hcω.comp (continuous_stopTime _)).comp continuous_real_toNNReal)
  have hz := Continuous.ext_on Rat.denseRange_cast hcont continuous_const
    (fun r ⟨q, hq⟩ => by rw [← hq]; exact hω q n)
  have := congrFun hz (stopTime (gramTraceStop G K ω) t : ℝ)
  simpa only [Real.toNNReal_coe] using this

theorem principalMinorSum_near_ae_forall_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ)
    (h0 : ∀ᵐ ω ∂Q, principalMinorSum k (G 0 ω).2 = 0) :
    ∀ᵐ ω ∂Q, ∀ (t : ℝ≥0) (K : ℝ),
      principalMinorSum k (stoppedProcess G (gramTraceStop G K) t ω).2 = 0 :=
  ae_forall_stopped_eq_zero (f := fun H => principalMinorSum k H.2) hG.continuous
    (contDiff_ek_snd k).continuous fun t K =>
      principalMinorSum_near_stopped_eq_zero hD0 hD hG k K h0 t

theorem principalMinorSum_far_ae_forall_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ)
    (h0 : ∀ᵐ ω ∂Q, principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0) :
    ∀ᵐ ω ∂Q, ∀ (t : ℝ≥0) (K : ℝ), principalMinorSum k
      ((stoppedProcess G (gramTraceStop G K) t ω).1 -
        (stoppedProcess G (gramTraceStop G K) t ω).2) = 0 :=
  ae_forall_stopped_eq_zero (f := fun H => principalMinorSum k (H.1 - H.2)) hG.continuous
    (contDiff_ek_fst_sub_snd k).continuous fun t K =>
      principalMinorSum_far_stopped_eq_zero hD0 hD hG k K h0 t

end BlockBand.SourceProcess.Stochastic.GramUniqueness
