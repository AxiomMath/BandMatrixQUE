module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartLip
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartGap
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.CongrMP
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankNoCreation
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealBridge
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Local stopped-law uniqueness for the Gram martingale problem on a fixed stratum

Fix ranks `r, r'`, a level `η > 0` and a radius `K`. The chart domain
`chartDom r r' η K = {y : ‖y‖ < K, e_r(B) > η, e_{r'}(M - B) > η}` (real Gram coordinates)
is a relatively compact open set (`isInteriorDomain_chartDom`).
* `ek_eq_zero_forall`: for a Gram MP solution with `e_k(B_0) = 0` a.s., `e_k(B_t) = 0` a.s. for
  every `t` (no rank creation, `principalMinorSum_near_stopped_eq_zero`, with `K → ∞`); same for
  `M - B`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u v

/-- The chart domain. -/
def chartDom (c : Type*) [Fintype c] [DecidableEq c] (r r' : ℕ) (η K : ℝ) :
    Set (Fin (gramDim c) → ℝ) :=
  {y | ‖y‖ < K ∧ η < principalMinorSum r (fromGramReal y).2 ∧
    η < principalMinorSum r' ((fromGramReal y).1 - (fromGramReal y).2)}

theorem isInteriorDomain_chartDom (r r' : ℕ) (η K : ℝ) :
    IsInteriorDomain (chartDom c r r' η K) univ := by
  refine ⟨?_, ?_, subset_univ _⟩
  · have e : chartDom c r r' η K = {y | ‖y‖ < K} ∩ ({y | η < principalMinorSum r (fromGramReal y).2} ∩
        {y | η < principalMinorSum r' ((fromGramReal y).1 - (fromGramReal y).2)}) := rfl
    rw [e]
    refine (isOpen_lt continuous_norm continuous_const).inter
      ((isOpen_lt continuous_const ?_).inter (isOpen_lt continuous_const ?_))
    · exact (contDiff_comp_fromGramReal (contDiff_ek_snd r)).continuous
    · exact (contDiff_comp_fromGramReal (contDiff_ek_fst_sub_snd r')).continuous
  · refine Bornology.IsBounded.isCompact_closure ((Metric.isBounded_closedBall (x := 0)
      (r := K)).subset fun y hy => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]; exact hy.1.le

/-- The trace bound on the chart domain. -/
def chartT (c : Type*) [Fintype c] [DecidableEq c] (K : ℝ) : ℝ :=
  Fintype.card c * (‖(fromGramReal (c := c))‖ * K) + 1

theorem re_trace_le_chartT {K : ℝ} {y : Fin (gramDim c) → ℝ} (hy : ‖y‖ < K) :
    ((fromGramReal y).1.trace).re ≤ chartT c K := by
  set G := fromGramReal y
  have hG : ‖G‖ ≤ ‖(fromGramReal (c := c))‖ * K :=
    ((fromGramReal (c := c)).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hy.le (norm_nonneg _))
  have hi : ∀ i, (G.1 i i).re ≤ ‖(fromGramReal (c := c))‖ * K := fun i =>
    (Complex.re_le_norm _).trans ((norm_entry_le _ _ _).trans ((norm_fst_le G).trans hG))
  calc (G.1.trace).re = ∑ i, (G.1 i i).re := by simp [Matrix.trace, Complex.re_sum]
    _ ≤ ∑ _i : c, ‖(fromGramReal (c := c))‖ * K := Finset.sum_le_sum fun i _ => hi i
    _ ≤ chartT c K := by simp [chartT]

theorem one_le_chartT {K : ℝ} (hK : 0 ≤ K) : 1 ≤ chartT c K := by
  unfold chartT
  have : 0 ≤ (Fintype.card c : ℝ) * (‖(fromGramReal (c := c))‖ * K) := by positivity
  linarith

/-- The spectral gap of the chart. -/
def chartδ (c : Type*) [Fintype c] [DecidableEq c] (r r' : ℕ) (η K : ℝ) : ℝ :=
  η / (2 ^ Fintype.card c * chartT c K ^ (r + r'))

/-- The set where a stratum solution lives. -/
def stratumSet (D : Matrix c c ℂ) (r r' : ℕ) : Set (Fin (gramDim c) → ℝ) :=
  {y | GramFeasible D (fromGramReal y) ∧ principalMinorSum (r + 1) (fromGramReal y).2 = 0 ∧
    principalMinorSum (r' + 1) ((fromGramReal y).1 - (fromGramReal y).2) = 0}

theorem chartGood_of_mem {D : Matrix c c ℂ} {r r' : ℕ} {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    {y : Fin (gramDim c) → ℝ} (hy : y ∈ stratumSet D r r' ∩ chartDom c r r' η K) :
    ChartGood D (chartδ c r r' η K) (fromGramReal y) := by
  have hT1 := one_le_chartT (c := c) hK
  have hle : ∀ k, k ≤ r + r' → chartδ c r r' η K ≤ η / (2 ^ Fintype.card c * chartT c K ^ k) :=
    fun k hk => div_le_div_of_nonneg_left hη.le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT1 hk) (by positivity))
  exact chartGood_of_stratum hy.1.1 hT1 (re_trace_le_chartT hy.2.1) hy.1.2.1 hy.2.2.1.le
    hy.1.2.2 hy.2.2.2.le (hle r (by omega)) (hle r' (by omega))

omit [DecidableEq c] in
theorem exists_lt_gramTraceStop {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω}
    (hc : Continuous fun t => G t ω) (t : ℝ≥0) :
    ∃ K : ℕ, (t : WithTop ℝ≥0) ≤ gramTraceStop G K ω := by
  have hcont : Continuous fun s => ((G s ω).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨K, hK⟩ := exists_nat_gt R
  refine ⟨K, le_iInf₂ fun s hs => WithTop.coe_le_coe.2 ?_⟩
  by_contra h
  have h1 := hR s ⟨zero_le, (not_le.1 h).le⟩
  rw [Real.norm_eq_abs] at h1
  linarith [le_abs_self ((G s ω).1.trace.re)]

/-- **Rank cannot be created**, at every time. -/
theorem ek_eq_zero_forall {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) (t : ℝ≥0) :
    ((∀ᵐ ω ∂Q, principalMinorSum k (G 0 ω).2 = 0) →
      ∀ᵐ ω ∂Q, principalMinorSum k (G t ω).2 = 0) ∧
    ((∀ᵐ ω ∂Q, principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0) →
      ∀ᵐ ω ∂Q, principalMinorSum k ((G t ω).1 - (G t ω).2) = 0) := by
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · filter_upwards [ae_all_iff.2 fun K : ℕ =>
      principalMinorSum_near_stopped_eq_zero hD0 hD hG k K h0 t, hG.continuous] with ω h hc
    obtain ⟨K, hK⟩ := exists_lt_gramTraceStop hc t
    have := h K
    rwa [stoppedProcess_eq_stopTime, stopTime_of_le hK] at this
  · filter_upwards [ae_all_iff.2 fun K : ℕ =>
      principalMinorSum_far_stopped_eq_zero hD0 hD hG k K h0 t, hG.continuous] with ω h hc
    obtain ⟨K, hK⟩ := exists_lt_gramTraceStop hc t
    have := h K
    rwa [stoppedProcess_eq_stopTime, stopTime_of_le hK] at this

/-- **A stratum solution solves the chart martingale problem.** -/
theorem isMPSolutionOn_chart {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
    (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {r r' : ℕ} (hB : ∀ᵐ ω ∂Q, principalMinorSum (r + 1) (G 0 ω).2 = 0)
    (hC : ∀ᵐ ω ∂Q, principalMinorSum (r' + 1) ((G 0 ω).1 - (G 0 ω).2) = 0) {η K : ℝ}
    (hη : 0 < η) (hK : 0 ≤ K) :
    IsMPSolutionOn Q 𝓖 (gramRealDrift D0 D)
      (fun y => chartSigma D0 D (chartδ c r r' η K) y *
        (chartSigma D0 D (chartδ c r r' η K) y).transpose)
      (chartDom c r r' η K) (fun t ω => toGramReal (G t ω)) := by
  have hδ : 0 < chartδ c r r' η K := by
    unfold chartδ; have := one_le_chartT (c := c) hK; positivity
  have hσc := (locallyLipschitz_chartSigma (c := c) D0 D hδ).continuous
  refine isMPSolutionOn_congr_on (isMPSolutionOn_gramReal hD hG) (subset_univ _)
    (isInteriorDomain_chartDom r r' η K).1 ?_ (hσc.matrix_mul hσc.matrix_transpose)
    (F := stratumSet D r r') (fun t => ?_) fun y hy =>
      (chartSigma_cov hD0.le hD hδ (chartGood_of_mem hη hK hy)).symm
  · exact continuous_pi fun i => continuous_pi fun j => by
      unfold gramRealCov realCovEntry
      split_ifs <;>
        first
        | exact (Complex.continuous_re.comp (((continuous_gramCovEntry D0 D _ _).comp
            continuous_fromGramReal').add ((continuous_gramCovEntry D0 D _ _).comp
              continuous_fromGramReal'))).div_const _
        | exact (Complex.continuous_im.comp (((continuous_gramCovEntry D0 D _ _).comp
            continuous_fromGramReal').sub ((continuous_gramCovEntry D0 D _ _).comp
              continuous_fromGramReal'))).div_const _
        | exact (Complex.continuous_im.comp (((continuous_gramCovEntry D0 D _ _).comp
            continuous_fromGramReal').add ((continuous_gramCovEntry D0 D _ _).comp
              continuous_fromGramReal'))).div_const _
        | exact (Complex.continuous_re.comp (((continuous_gramCovEntry D0 D _ _).comp
            continuous_fromGramReal').sub ((continuous_gramCovEntry D0 D _ _).comp
              continuous_fromGramReal'))).div_const _
  · filter_upwards [hG.feasible, (ek_eq_zero_forall hD0 hD hG (r + 1) t).1 hB,
      (ek_eq_zero_forall hD0 hD hG (r' + 1) t).2 hC] with ω h1 h2 h3
    simp only [stratumSet, mem_ofPred_eq, fromGramReal_toGramReal]
    exact ⟨h1 t, h2, h3⟩

omit [DecidableEq c] in
theorem map_toGramReal_zero {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) :
    Q.map (fun ω => toGramReal (G 0 ω)) = (Q.map (G 0)).map toGramReal := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := Prod.borelSpace
  rw [Measure.map_map continuous_toGramReal.measurable
    (((hG.adapted 0).mono (𝓖.le 0)).measurable)]
  rfl

/-- **Local stopped-law uniqueness on a chart domain.** -/
theorem chart_stopped_law_eq {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {r r' : ℕ} {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {G₁ : ℝ≥0 → Ω₁ → Matrix c c ℂ × Matrix c c ℂ} (hG₁ : IsGramMartingaleSolution Q₁ 𝓖₁ D0 D G₁)
    (hB₁ : ∀ᵐ ω ∂Q₁, principalMinorSum (r + 1) (G₁ 0 ω).2 = 0)
    (hC₁ : ∀ᵐ ω ∂Q₁, principalMinorSum (r' + 1) ((G₁ 0 ω).1 - (G₁ 0 ω).2) = 0)
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {G₂ : ℝ≥0 → Ω₂ → Matrix c c ℂ × Matrix c c ℂ} (hG₂ : IsGramMartingaleSolution Q₂ 𝓖₂ D0 D G₂)
    (hB₂ : ∀ᵐ ω ∂Q₂, principalMinorSum (r + 1) (G₂ 0 ω).2 = 0)
    (hC₂ : ∀ᵐ ω ∂Q₂, principalMinorSum (r' + 1) ((G₂ 0 ω).1 - (G₂ 0 ω).2) = 0)
    (h0 : Q₁.map (G₁ 0) = Q₂.map (G₂ 0)) :
    Q₁.map (fun ω t => stoppedProcess (fun t ω => toGramReal (G₁ t ω))
        (exitTimeFrom (chartDom c r r' η K) fun t ω => toGramReal (G₁ t ω)) t ω) =
      Q₂.map (fun ω t => stoppedProcess (fun t ω => toGramReal (G₂ t ω))
        (exitTimeFrom (chartDom c r r' η K) fun t ω => toGramReal (G₂ t ω)) t ω) := by
  have hδ : 0 < chartδ c r r' η K := by
    unfold chartδ; have := one_le_chartT (c := c) hK; positivity
  exact UniquenessDeg.stoppedMartingaleProblemUniquenessU_holds.{u, v} (gramDim c)
    (chartNoiseDim c) (gramRealDrift D0 D) (chartSigma D0 D (chartδ c r r' η K)) univ
    (chartDom c r r' η K) isOpen_univ
    (locallyLipschitzOn_univ.2 (locallyLipschitz_gramRealDrift D0 D))
    (locallyLipschitzOn_univ.2 (locallyLipschitz_chartSigma D0 D hδ))
    (isInteriorDomain_chartDom r r' η K) Ω₁ Q₁ 𝓖₁ (fun t ω => toGramReal (G₁ t ω))
    Ω₂ Q₂ 𝓖₂ (fun t ω => toGramReal (G₂ t ω)) (isMPSolutionOn_chart hD0 hD hG₁ hB₁ hC₁ hη hK)
    (isMPSolutionOn_chart hD0 hD hG₂ hB₂ hC₂ hη hK)
    (by rw [map_toGramReal_zero hG₁, map_toGramReal_zero hG₂, h0])

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
