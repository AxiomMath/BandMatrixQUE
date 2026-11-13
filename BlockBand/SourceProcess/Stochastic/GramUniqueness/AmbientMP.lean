module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientLocal
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Martingale-problem clauses of a semimartingale at a stopping time

For a continuous semimartingale `Y` with characteristics `(β, α)` and a stopping time, the
stopped compensated coordinates (`hasMM_mpCompensated_stopped`) and the stopped compensated
products (`hasMM_mpBracket_stopped`) have martingale modifications.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem continuous_mpCompensated_of_continuous (hb : Continuous b) {ω : Ω}
    (hc : Continuous fun t => Y t ω) (i : Fin d) :
    Continuous fun t => mpCompensated b Y i t ω :=
  (((continuous_apply i).comp hc).sub continuous_const).sub
    (continuous_setIntegral_Ioc (g := fun u => b (Y u ω) i) fun t =>
      integrableOn_Ioc_of_continuous (((continuous_apply i).comp hb).comp hc) t)

theorem hasMM_mpCompensated_stopped (hS : IsContinuousSemimartingale Q 𝓖 Y β α)
    (hβ : ∀ᵐ ω ∂Q, ∀ t, β t ω = b (Y t ω)) (hb : Continuous b) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) (i : Fin d)
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |stoppedProcess (mpCompensated b Y i) ρ s ω| ≤ C) :
    HasMartingaleModification Q 𝓖 (stoppedProcess (mpCompensated b Y i) ρ) := by
  obtain ⟨τ, -, hτlim, hloc⟩ := hS.localizing
  have heq : ∀ᵐ ω ∂Q, ∀ t, smCompensated Y β i t ω = mpCompensated b Y i t ω := by
    filter_upwards [hβ] with ω h t
    simp only [smCompensated, mpCompensated, h]
  refine hasMartingaleModification_stopped_of_localized hτlim (fun n => ?_) ?_ hρ hbd
  · obtain ⟨M, hM, hMX⟩ := (hloc n).1 i
    refine ⟨M, hM, fun t => (hMX t).trans ?_⟩
    filter_upwards [heq] with ω h
    simp only [stoppedProcess, h]
  · filter_upwards [hS.continuous] with ω hc
    exact continuous_mpCompensated_of_continuous hb hc i

theorem hasMM_mpBracket_stopped (hS : IsContinuousSemimartingale Q 𝓖 Y β α)
    (hβ : ∀ᵐ ω ∂Q, ∀ t, β t ω = b (Y t ω)) (hα : ∀ᵐ ω ∂Q, ∀ t, α t ω = a (Y t ω))
    (hb : Continuous b) (ha : Continuous a) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) (i j : Fin d)
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |stoppedProcess (fun t ω =>
      mpCompensated b Y i t ω * mpCompensated b Y j t ω -
        ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) ρ s ω| ≤ C) :
    HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
      mpCompensated b Y i t ω * mpCompensated b Y j t ω -
        ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) ρ) := by
  obtain ⟨τ, -, hτlim, hloc⟩ := hS.localizing
  have heq : ∀ᵐ ω ∂Q, ∀ t, smCompensated Y β i t ω * smCompensated Y β j t ω -
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j = mpCompensated b Y i t ω *
        mpCompensated b Y j t ω - ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j := by
    filter_upwards [hβ, hα] with ω h h' t
    simp only [smCompensated, mpCompensated, h, h']
  refine hasMartingaleModification_stopped_of_localized hτlim (fun n => ?_) ?_ hρ hbd
  · obtain ⟨M, hM, hMX⟩ := (hloc n).2 i j
    refine ⟨M, hM, fun t => (hMX t).trans ?_⟩
    filter_upwards [heq] with ω h
    simp only [stoppedProcess, h]
  · filter_upwards [hS.continuous] with ω hc
    have hai : Continuous fun u => a (Y u ω) i j :=
      (ha.comp hc).matrix_elem i j
    exact ((continuous_mpCompensated_of_continuous hb hc i).mul
      (continuous_mpCompensated_of_continuous hb hc j)).sub
      (continuous_setIntegral_Ioc (g := fun u => a (Y u ω) i j) fun t =>
        integrableOn_Ioc_of_continuous hai t)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
