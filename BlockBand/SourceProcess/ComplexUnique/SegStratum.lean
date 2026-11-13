module

public import BlockBand.SourceProcess.ComplexUnique.SegExhaust
public import BlockBand.SourceProcess.Stochastic.Uniqueness.LawLimit
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Exhaust

/-!
# Uniqueness of the law at the horizon on a fixed stratum

**`stratum_law_eq`**: two (restarted) solutions of the joint real martingale problem in
`{t < h}` (`D₀ ≥ 0`, signature `𝖣`), with time coordinate `u ∧ h`, living a.s. in
`segF D r r' h`, of exact ranks `(r, r')` before `h`, and with equal initial laws, have equal laws
at the horizon `h`. Proof: on each chart domain `segW r r' h n` the joint chart noise matches the
brackets (`segAgree`), so the stopped laws agree (`stopped_law_eq`); the stopped values
at `h` converge a.s. to the values at `h` (`tendsto_stop_segW`); limits of a.s. convergent
sequences with equal laws have equal laws (`Uniqueness.map_eq_of_tendsto_ae`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u v

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

/-- **Equal laws at the horizon on a stratum.** -/
theorem stratum_law_eq {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) {D : Matrix (SrcCol K π) (SrcCol K π) ℂ}
    (hD : IsSignature D) {r r' : ℕ} {h : ℝ≥0}
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {Y₁ : ℝ≥0 → Ω₁ → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ}
    (hY₁ : IsMPSolutionOn Q₁ 𝓖₁ (realDrift (jβ D0 D)) (realCov (jΓ D0 η D) (jΓ' D0 η D))
      {y | tOf y < h} Y₁)
    (ht₁ : ∀ ω u, tOf (Y₁ u ω) = ((min u h : ℝ≥0) : ℝ)) (hF₁ : ∀ u, ∀ᵐ ω ∂Q₁, Y₁ u ω ∈ segF D r r' h)
    (hp₁ : ∀ᵐ ω ∂Q₁, ∀ u < h, 0 < principalMinorSum r (gOf (Y₁ u ω)).2 ∧
      0 < principalMinorSum r' ((gOf (Y₁ u ω)).1 - (gOf (Y₁ u ω)).2))
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {Y₂ : ℝ≥0 → Ω₂ → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ}
    (hY₂ : IsMPSolutionOn Q₂ 𝓖₂ (realDrift (jβ D0 D)) (realCov (jΓ D0 η D) (jΓ' D0 η D))
      {y | tOf y < h} Y₂)
    (ht₂ : ∀ ω u, tOf (Y₂ u ω) = ((min u h : ℝ≥0) : ℝ)) (hF₂ : ∀ u, ∀ᵐ ω ∂Q₂, Y₂ u ω ∈ segF D r r' h)
    (hp₂ : ∀ᵐ ω ∂Q₂, ∀ u < h, 0 < principalMinorSum r (gOf (Y₂ u ω)).2 ∧
      0 < principalMinorSum r' ((gOf (Y₂ u ω)).1 - (gOf (Y₂ u ω)).2))
    (h0 : Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0)) :
    Q₁.map (Y₁ h) = Q₂.map (Y₂ h) := by
  have hYa₁ : ∀ t, Measurable[𝓖₁ t] (Y₁ t) := fun t => (hY₁.adapted t).measurable
  have hYa₂ : ∀ t, Measurable[𝓖₂ t] (Y₂ t) := fun t => (hY₂.adapted t).measurable
  have hWi := fun n : ℕ => isInteriorDomain_segW (K := K) (π := π) r r' h n
  refine map_eq_of_tendsto_ae
    (f₁ := fun n ω => stoppedProcess Y₁ (exitTimeFrom (segW K π r r' h n) Y₁) h ω)
    (f₂ := fun n ω => stoppedProcess Y₂ (exitTimeFrom (segW K π r r' h n) Y₂) h ω)
    (fun n => (measurable_pi_apply h).comp_aemeasurable
      (aemeasurable_stopped hYa₁ hY₁.continuous (hWi n).1))
    (fun n => (measurable_pi_apply h).comp_aemeasurable
      (aemeasurable_stopped hYa₂ hY₂.continuous (hWi n).1)) ?_ ?_ fun n => ?_
  · filter_upwards [hY₁.continuous, hp₁] with ω hc hp
    exact tendsto_stop_segW hc (ht₁ ω) hp
  · filter_upwards [hY₂.continuous, hp₂] with ω hc hp
    exact tendsto_stop_segW hc (ht₂ ω) hp
  · have hW : IsInteriorDomain (segW K π r r' h n) univ :=
      ⟨(hWi n).1, (hWi n).2.1, subset_univ _⟩
    have hl := stopped_law_eq (locallyLipschitz_jβ D0 D)
      (locallyLipschitz_jNoise D0 η D (segδ_pos (SrcCol K π) r r' n))
      (continuous_jΓ D0 η D) (continuous_jΓ' D0 η D) hW (subset_closure.trans (hWi n).2.2)
      (segAgree hD0 η hD r r' h n) hY₁ hF₁ hY₂ hF₂ h0
    have e₁ := AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply h).aemeasurable
      (aemeasurable_stopped hYa₁ hY₁.continuous (hWi n).1)
    have e₂ := AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply h).aemeasurable
      (aemeasurable_stopped hYa₂ hY₂.continuous (hWi n).1)
    exact e₁.symm.trans ((congrArg (fun μ => μ.map fun f => f h) hl).trans e₂)

end BlockBand.SourceProcess.ComplexUnique
