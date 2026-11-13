module

public import BlockBand.Transmission.Dual.GProduct

/-!
# The product of two martingale-problem solutions solves the decoupled problem

`isMPSolutionOn_prod`: on `Q₁ ⊗ Q₂` with the product filtration, `(Y₁, Y₂)` solves the
martingale problem with drift `(b₁, b₂)` and covariance `diag(a₁, a₂)` on `U₁ × U₂`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d₁ d₂ : ℕ} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
  {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
  {Y₁ : ℝ≥0 → Ω₁ → Fin d₁ → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin d₂ → ℝ}
  {b₁ : (Fin d₁ → ℝ) → Fin d₁ → ℝ} {b₂ : (Fin d₂ → ℝ) → Fin d₂ → ℝ}
  {a₁ : (Fin d₁ → ℝ) → Matrix (Fin d₁) (Fin d₁) ℝ} {a₂ : (Fin d₂ → ℝ) → Matrix (Fin d₂) (Fin d₂) ℝ}
  {U₁ : Set (Fin d₁ → ℝ)} {U₂ : Set (Fin d₂ → ℝ)}

omit [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂] in
theorem measurable_prodPath (h₁ : ∀ t, StronglyMeasurable[𝓖₁ t] (Y₁ t))
    (h₂ : ∀ t, StronglyMeasurable[𝓖₂ t] (Y₂ t)) (t : ℝ≥0) :
    Measurable[prodFiltration 𝓖₁ 𝓖₂ t] (prodPath Y₁ Y₂ t) := by
  refine (@measurable_pi_iff (Ω₁ × Ω₂) (Fin (d₁ + d₂)) (fun _ => ℝ) (prodFiltration 𝓖₁ 𝓖₂ t) _
    _).2 fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [prodPath, Fin.append_left]
    exact ((measurable_pi_apply i).comp (h₁ t).measurable).comp
      (measurable_fst_prodFiltration t)
  · simp only [prodPath, Fin.append_right]
    exact ((measurable_pi_apply j).comp (h₂ t).measurable).comp
      (measurable_snd_prodFiltration t)

theorem ae_continuous_prodPath (h₁ : ∀ᵐ ω ∂Q₁, Continuous fun t => Y₁ t ω)
    (h₂ : ∀ᵐ ω ∂Q₂, Continuous fun t => Y₂ t ω) :
    ∀ᵐ x ∂(Q₁.prod Q₂), Continuous fun t => prodPath Y₁ Y₂ t x := by
  filter_upwards [ae_fst h₁, ae_snd h₂] with x hx₁ hx₂
  refine continuous_pi fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [prodPath, Fin.append_left]; exact (continuous_apply i).comp hx₁
  · simp only [prodPath, Fin.append_right]; exact (continuous_apply j).comp hx₂

/-- **The product of two solutions solves the decoupled martingale problem** on `U₁ × U₂`, for
the product filtration and `Q₁ ⊗ Q₂`. -/
theorem isMPSolutionOn_prod (h₁ : IsMPSolutionOn Q₁ 𝓖₁ b₁ a₁ U₁ Y₁)
    (h₂ : IsMPSolutionOn Q₂ 𝓖₂ b₂ a₂ U₂ Y₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hb₁ : ContinuousOn b₁ U₁) (ha₁ : ContinuousOn a₁ U₁) (hb₂ : ContinuousOn b₂ U₂)
    (ha₂ : ContinuousOn a₂ U₂) :
    IsMPSolutionOn (Q₁.prod Q₂) (prodFiltration 𝓖₁ 𝓖₂) (prodDrift b₁ b₂) (prodDiff a₁ a₂)
      (prodDomain U₁ U₂) (prodPath Y₁ Y₂) := by
  have hm := measurable_prodPath h₁.adapted h₂.adapted
  have hc := ae_continuous_prodPath h₁.continuous h₂.continuous
  -- the factor processes, stopped at factor domains, with their continuity
  have C₁ : ∀ W₁, IsInteriorDomain W₁ U₁ → ∀ i, ∀ᵐ x ∂(Q₁.prod Q₂), Continuous fun t =>
      stoppedProcess (mpCompensated b₁ Y₁ i) (exitTimeFrom W₁ Y₁) t x.1 := fun W₁ hW₁ i =>
    ae_fst (h₁.continuous.mono fun ω hω =>
      continuous_stopped_mpCompensated hW₁.1 hW₁.2.2 hb₁ hω i)
  have C₂ : ∀ W₂, IsInteriorDomain W₂ U₂ → ∀ j, ∀ᵐ x ∂(Q₁.prod Q₂), Continuous fun t =>
      stoppedProcess (mpCompensated b₂ Y₂ j) (exitTimeFrom W₂ Y₂) t x.2 := fun W₂ hW₂ j =>
    ae_snd (h₂.continuous.mono fun ω hω =>
      continuous_stopped_mpCompensated hW₂.1 hW₂.2.2 hb₂ hω j)
  refine ⟨fun t => (hm t).stronglyMeasurable, hc, fun W hW k => ?_, fun W hW k l => ?_⟩
  all_goals
    obtain ⟨⟨W₁, hW₁, hl⟩, ⟨W₂, hW₂, hr⟩⟩ := exists_factor_domains hU₁ hU₂ hW
    have e₁ : ∀ x t, stopTime (exitTimeFrom W₁ Y₁ x.1)
        (stopTime (exitTimeFrom W (prodPath Y₁ Y₂) x) t) =
        stopTime (exitTimeFrom W (prodPath Y₁ Y₂) x) t := fun x t =>
      stopTime_stopTime_of_le (exitTime_prod_le_fst hl x) t
    have e₂ : ∀ x t, stopTime (exitTimeFrom W₂ Y₂ x.2)
        (stopTime (exitTimeFrom W (prodPath Y₁ Y₂) x) t) =
        stopTime (exitTimeFrom W (prodPath Y₁ Y₂) x) t := fun x t =>
      stopTime_stopTime_of_le (exitTime_prod_le_snd hr x) t
  · -- drift
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine hasMM_stop_congr (hasMartingaleModification_lift_fst (h₁.drift W₁ hW₁ i))
        (C₁ W₁ hW₁ i) hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₁, mpCompensated_prod_castAdd]
    · refine hasMM_stop_congr (hasMartingaleModification_lift_snd (h₂.drift W₂ hW₂ j))
        (C₂ W₂ hW₂ j) hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₂, mpCompensated_prod_natAdd]
  · -- brackets
    refine Fin.addCases (fun i => Fin.addCases (fun j => ?_) (fun j => ?_) l)
      (fun i => Fin.addCases (fun j => ?_) (fun j => ?_) l) k
    · refine hasMM_stop_congr (hasMartingaleModification_lift_fst (h₁.bracket W₁ hW₁ i j))
        (ae_fst (h₁.continuous.mono fun ω hω =>
          continuous_stopped_bracket hW₁.1 hW₁.2.2 hb₁ ha₁ hω i j)) hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₁, mpCompensated_prod_castAdd, prodDiff_cc,
        leftPart_prodPath]
    · refine hasMM_stop_congr (hasMM_mul_lift (h₁.drift W₁ hW₁ i) (h₂.drift W₂ hW₂ j))
        (by filter_upwards [C₁ W₁ hW₁ i, C₂ W₂ hW₂ j] with x hx hy using hx.mul hy)
        hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₁, e₂, mpCompensated_prod_castAdd,
        mpCompensated_prod_natAdd, prodDiff_cn, integral_zero, sub_zero]
    · refine hasMM_stop_congr (hasMM_mul_lift (h₁.drift W₁ hW₁ j) (h₂.drift W₂ hW₂ i))
        (by filter_upwards [C₁ W₁ hW₁ j, C₂ W₂ hW₂ i] with x hx hy using hx.mul hy)
        hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₁, e₂, mpCompensated_prod_castAdd,
        mpCompensated_prod_natAdd, prodDiff_nc, integral_zero, sub_zero, mul_comm]
    · refine hasMM_stop_congr (hasMartingaleModification_lift_snd (h₂.bracket W₂ hW₂ i j))
        (ae_snd (h₂.continuous.mono fun ω hω =>
          continuous_stopped_bracket hW₂.1 hW₂.2.2 hb₂ ha₂ hω i j)) hm hc hW.1 fun t x => ?_
      simp only [stoppedProcess_eq_stopTime, e₂, mpCompensated_prod_natAdd, prodDiff_nn,
        rightPart_prodPath]

end BlockBand.Transmission.Dual.G
