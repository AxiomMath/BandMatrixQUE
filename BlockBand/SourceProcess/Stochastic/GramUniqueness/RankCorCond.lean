module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankNoCreation
public import Mathlib.Probability.ConditionalProbability
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Corollary(a)): conditioning a Gram MP solution on an `𝓖₀`-event

* `martingale_cond`: a martingale for `Q` is a martingale for `Q[|A]` when `A ∈ 𝓖₀`, `Q A ≠ 0`.
* `isGramMartingaleSolution_cond`: a feasible Gram MP solution for `Q` is one for `Q[|A]`.
* `principalMinorSum_{near,far}_stopped_eq_zero_on`: random initial rank for no rank creation. If
  `e_k(B_0) = 0` a.s. on `A ∈ 𝓖₀`, then `e_k(B_{t∧σ_K}) = 0` a.s. on `A`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [IsFiniteMeasure Q] in
theorem ae_cond_of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂Q, p ω) (A : Set Ω) : ∀ᵐ ω ∂Q[|A], p ω :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

theorem martingale_cond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {N : ℝ≥0 → Ω → E} (hN : Martingale N 𝓖 Q) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (hA0 : Q A ≠ 0) : Martingale N 𝓖 (Q[|A]) := by
  have := cond_isProbabilityMeasure (μ := Q) hA0
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  have hc : (Q A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hA0
  have hint : ∀ t, Integrable (N t) (Q[|A]) := fun t =>
    ((hN.integrable t).restrict).smul_measure hc
  refine ⟨hN.1, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hint t)
    (fun B _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (hN.1 s).aestronglyMeasurable).symm
  have hB' : MeasurableSet B := 𝓖.le s _ hB
  rw [ProbabilityTheory.cond, Measure.restrict_smul,
    integral_smul_measure, integral_smul_measure, Measure.restrict_restrict hB',
    hN.setIntegral_eq hst (hB.inter (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ s) _ hA))]

theorem isGramMartingaleSolution_cond {c : Type*} [Fintype c] {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {A : Set Ω} (hA : MeasurableSet[𝓖 0] A) (hA0 : Q A ≠ 0) :
    IsGramMartingaleSolution (Q[|A]) 𝓖 D0 D G where
  adapted := hG.adapted
  continuous := ae_cond_of_ae hG.continuous A
  feasible := ae_cond_of_ae hG.feasible A
  drift K e := by
    obtain ⟨N, hN, hNX⟩ := hG.drift K e
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  bracket K e e' := by
    obtain ⟨N, hN, hNX⟩ := hG.bracket K e e'
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩

theorem ae_of_ae_cond {A : Set Ω} (hA : MeasurableSet A) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂Q[|A], p ω) : ∀ᵐ ω ∂Q, ω ∈ A → p ω := by
  rw [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2
    (measure_ne_top Q A))] at h
  exact (ae_restrict_iff' hA).1 h

variable {c : Type*} [Fintype c] [DecidableEq c]

theorem principalMinorSum_near_stopped_eq_zero_on [IsProbabilityMeasure Q] {D0 : ℝ}
    (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    (k : ℕ) (K : ℝ) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (h0 : ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k (G 0 ω).2 = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k (stoppedProcess G (gramTraceStop G K) t ω).2 = 0 := by
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  by_cases hA0 : Q A = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with ω hω h
    exact absurd h hω
  have := cond_isProbabilityMeasure (μ := Q) hA0
  have h0' : ∀ᵐ ω ∂Q[|A], principalMinorSum k (G 0 ω).2 = 0 := by
    rw [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2
      (measure_ne_top Q A))]
    exact (ae_restrict_iff' hA').2 h0
  exact ae_of_ae_cond hA'
    (principalMinorSum_near_stopped_eq_zero hD0 hD (isGramMartingaleSolution_cond hG hA hA0) k K
      h0' t)

theorem principalMinorSum_far_stopped_eq_zero_on [IsProbabilityMeasure Q] {D0 : ℝ}
    (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    (k : ℕ) (K : ℝ) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (h0 : ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, ω ∈ A → principalMinorSum k ((stoppedProcess G (gramTraceStop G K) t ω).1 -
      (stoppedProcess G (gramTraceStop G K) t ω).2) = 0 := by
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  by_cases hA0 : Q A = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with ω hω h
    exact absurd h hω
  have := cond_isProbabilityMeasure (μ := Q) hA0
  have h0' : ∀ᵐ ω ∂Q[|A], principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0 := by
    rw [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2
      (measure_ne_top Q A))]
    exact (ae_restrict_iff' hA').2 h0
  exact ae_of_ae_cond hA'
    (principalMinorSum_far_stopped_eq_zero hD0 hD (isGramMartingaleSolution_cond hG hA hA0) k K
      h0' t)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
