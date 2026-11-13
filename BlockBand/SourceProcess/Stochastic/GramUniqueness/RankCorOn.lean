module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorCond
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorCreation
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Corollary: no rank creation on an `𝓖₀`-event, for all times and trace levels

`principalMinorSum_near_ae_forall_eq_zero_on`, `principalMinorSum_far_ae_forall_eq_zero_on`: if
`e_k(B_0) = 0` a.s. on `A ∈ 𝓖₀`, then a.s. on `A`, `e_k(B_{t∧σ_K}) = 0` for all `t` and `K`; the
same holds for `M − B`. The proof conditions on `A` (`isGramMartingaleSolution_cond`) and applies
`principalMinorSum_near_ae_forall_eq_zero`, `principalMinorSum_far_ae_forall_eq_zero` under `Q[|A]`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {c : Type*} [Fintype c] [DecidableEq c]

theorem ae_cond_of_ae_on {A : Set Ω} (hA : MeasurableSet A) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂Q, ω ∈ A → p ω) : ∀ᵐ ω ∂Q[|A], p ω := by
  rw [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2
    (measure_ne_top Q A))]
  exact (ae_restrict_iff' hA).2 h

theorem principalMinorSum_near_ae_forall_eq_zero_on {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) {A : Set Ω}
    (hA : MeasurableSet[𝓖 0] A) (h0 : ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k (G 0 ω).2 = 0) :
    ∀ᵐ ω ∂Q, ω ∈ A → ∀ (t : ℝ≥0) (K : ℝ),
      principalMinorSum k (stoppedProcess G (gramTraceStop G K) t ω).2 = 0 := by
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  by_cases hA0 : Q A = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with ω hω h
    exact absurd h hω
  have := cond_isProbabilityMeasure (μ := Q) hA0
  exact ae_of_ae_cond hA' (principalMinorSum_near_ae_forall_eq_zero hD0 hD
    (isGramMartingaleSolution_cond hG hA hA0) k (ae_cond_of_ae_on hA' h0))

theorem principalMinorSum_far_ae_forall_eq_zero_on {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) {A : Set Ω}
    (hA : MeasurableSet[𝓖 0] A)
    (h0 : ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0) :
    ∀ᵐ ω ∂Q, ω ∈ A → ∀ (t : ℝ≥0) (K : ℝ), principalMinorSum k
      ((stoppedProcess G (gramTraceStop G K) t ω).1 -
        (stoppedProcess G (gramTraceStop G K) t ω).2) = 0 := by
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  by_cases hA0 : Q A = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with ω hω h
    exact absurd h hω
  have := cond_isProbabilityMeasure (μ := Q) hA0
  exact ae_of_ae_cond hA' (principalMinorSum_far_ae_forall_eq_zero hD0 hD
    (isGramMartingaleSolution_cond hG hA hA0) k (ae_cond_of_ae_on hA' h0))

end BlockBand.SourceProcess.Stochastic.GramUniqueness
