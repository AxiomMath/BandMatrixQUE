module

public import BlockBand.SourceProcess.ComplexUnique.RealCoord
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorCond
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.CongrMP
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.Main

/-!
# Conditioning and local stopped-law uniqueness for complex-coordinate martingale problems

* `isMPSolutionOn_cond`: a martingale-problem solution stays one after conditioning on an
  `𝓖₀`-event of positive mass (`martingale_cond`).
* **`stopped_law_eq`**: two solutions of the `(realDrift β, realCov Γ Γ')` problem in `U` living
  a.s. in a set `F`, where on `F ∩ W` the complex noises `n_a` (locally Lipschitz, like `β`) have
  brackets `Γ`, `Γ'`, have equal laws of their paths stopped at the exit from `W` (relatively
  compact, `W ⊆ U`) once their initial laws agree: congruence `isMPSolutionOn_congr_on` to
  `σσᵀ` (`realSigma_cov`), then stopped martingale-problem uniqueness for locally Lipschitz
  coefficients in every universe (`UniquenessDeg.stoppedMartingaleProblemUniquenessU_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u v

theorem isMPSolutionOn_cond {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {U : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : IsMPSolutionOn Q 𝓗 b a U Y)
    {A : Set Ω} (hA : MeasurableSet[𝓗 0] A) (hA0 : Q A ≠ 0) :
    IsMPSolutionOn (Q[|A]) 𝓗 b a U Y := by
  have hac : Q[|A] ≪ Q := cond_absolutelyContinuous
  refine ⟨hY.adapted, hac.ae_le hY.continuous, fun W hW i => ?_, fun W hW i j => ?_⟩
  · obtain ⟨N, hN, hNX⟩ := hY.drift W hW i
    exact ⟨N, martingale_cond hN hA hA0, fun t => hac.ae_le (hNX t)⟩
  · obtain ⟨N, hN, hNX⟩ := hY.bracket W hW i j
    exact ⟨N, martingale_cond hN hA hA0, fun t => hac.ae_le (hNX t)⟩

variable {κ : Type*} [Fintype κ] {ν : Type*} [Fintype ν]

/-- **Local stopped-law uniqueness from a matching complex noise.** -/
theorem stopped_law_eq {β : (κ → ℂ) → κ → ℂ} {Γ Γ' : (κ → ℂ) → κ → κ → ℂ}
    {n : ν → (κ → ℂ) → κ → ℂ} (hβ : LocallyLipschitz β) (hn : ∀ a, LocallyLipschitz (n a))
    (hΓ : Continuous Γ) (hΓ' : Continuous Γ') {U W F : Set (Fin (rDim κ) → ℝ)}
    (hW : IsInteriorDomain W univ) (hWU : W ⊆ U)
    (hagree : ∀ y ∈ F ∩ W, ∀ p q, (∑ a, n a (zOf y) p * n a (zOf y) q = Γ (zOf y) p q) ∧
      ∑ a, n a (zOf y) p * star (n a (zOf y) q) = Γ' (zOf y) p q)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {Y₁ : ℝ≥0 → Ω₁ → Fin (rDim κ) → ℝ}
    (hY₁ : IsMPSolutionOn Q₁ 𝓖₁ (realDrift β) (realCov Γ Γ') U Y₁)
    (hF₁ : ∀ t, ∀ᵐ ω ∂Q₁, Y₁ t ω ∈ F)
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (rDim κ) → ℝ}
    (hY₂ : IsMPSolutionOn Q₂ 𝓖₂ (realDrift β) (realCov Γ Γ') U Y₂)
    (hF₂ : ∀ t, ∀ᵐ ω ∂Q₂, Y₂ t ω ∈ F)
    (h0 : Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0)) :
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) := by
  have hσ := locallyLipschitz_realSigma hn
  have hσc := hσ.continuous
  have ha : Continuous (realCov Γ Γ') := continuous_realCov hΓ hΓ'
  have hag : ∀ y ∈ F ∩ W, realCov Γ Γ' y = realSigma n y * (realSigma n y).transpose :=
    fun y hy => (realSigma_cov n Γ Γ' y (fun p q => (hagree y hy p q).1)
      (fun p q => (hagree y hy p q).2)).symm
  exact UniquenessDeg.stoppedMartingaleProblemUniquenessU_holds.{u, v} (rDim κ) (Fintype.card ν)
    (realDrift β) (realSigma n) univ W isOpen_univ
    (locallyLipschitzOn_univ.2 (locallyLipschitz_realDrift hβ))
    (locallyLipschitzOn_univ.2 hσ) hW Ω₁ Q₁ 𝓖₁ Y₁ Ω₂ Q₂ 𝓖₂ Y₂
    (isMPSolutionOn_congr_on hY₁ hWU hW.1 ha (hσc.matrix_mul hσc.matrix_transpose) hF₁ hag)
    (isMPSolutionOn_congr_on hY₂ hWU hW.1 ha (hσc.matrix_mul hσc.matrix_transpose) hF₂ hag) h0

end BlockBand.SourceProcess.ComplexUnique
