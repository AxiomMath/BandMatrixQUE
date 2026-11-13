module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepMain
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank creation: neither Gram rank can increase

For a feasible Gram martingale-problem solution (sample space in any universe), `0 < D₀`, a
signature `𝖣`, every `k` and trace level `K`: if `e_k(B_0) = 0` a.s. then `e_k(B_{t∧σ_K}) = 0` a.s.
for all `t` (`principalMinorSum_near_stopped_eq_zero`), and likewise for `C = M − B`
(`principalMinorSum_far_stopped_eq_zero`). Since `e_k` of a positive matrix vanishes iff its rank
is `< k`, neither `rank B` nor `rank (M − B)` can increase before `σ_K`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u

theorem principalMinorSum_near_stopped_eq_zero {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) (K : ℝ)
    (h0 : ∀ᵐ ω ∂Q, principalMinorSum k (G 0 ω).2 = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, principalMinorSum k (stoppedProcess G (gramTraceStop G K) t ω).2 = 0 := by
  obtain ⟨C, hC⟩ := gramGenerator_rankBarrier hD0 hD k K
  refine stopped_eq_zero_of_barrier (f := fun H => principalMinorSum k H.2) hD hG
    (contDiff_ek_snd k) (le_max_right C 0)
    (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).1) (fun H hH hK => ?_) h0 t
  exact (hC H hH hK).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (principalMinorSum_nonneg_of_feasible hH k).1)

theorem principalMinorSum_far_stopped_eq_zero {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} (hD0 : 0 < D0)
    {D : Matrix c c ℂ} (hD : IsSignature D) {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) (k : ℕ) (K : ℝ)
    (h0 : ∀ᵐ ω ∂Q, principalMinorSum k ((G 0 ω).1 - (G 0 ω).2) = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, principalMinorSum k ((stoppedProcess G (gramTraceStop G K) t ω).1 -
      (stoppedProcess G (gramTraceStop G K) t ω).2) = 0 := by
  obtain ⟨C, hC⟩ := gramGenerator_rankBarrier hD0 hD k K
  refine stopped_eq_zero_of_barrier (f := fun H => principalMinorSum k (H.1 - H.2)) hD hG
    (contDiff_ek_fst_sub_snd k) (le_max_right C 0)
    (fun H hH => (principalMinorSum_nonneg_of_feasible hH k).2) (fun H hH hK => ?_) h0 t
  exact (hC H hH hK).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (principalMinorSum_nonneg_of_feasible hH k).2)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
