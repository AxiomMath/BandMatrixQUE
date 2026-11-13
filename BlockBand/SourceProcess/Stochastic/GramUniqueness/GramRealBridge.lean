module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealMP
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram martingale problem ⇒ real-coordinate martingale problem

`isMPSolutionOn_gramReal`: a feasible Gram
martingale-problem solution has real coordinates solving `IsMPSolutionOn Q 𝓖 (gramRealDrift D0 𝖣)
(gramRealCov D0 𝖣) univ`. Only `𝖣ᴴ = 𝖣` is used from the signature hypothesis.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The real compensated products along a feasible continuous path. -/
theorem mpBracket_gramReal {Ω : Type*} {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {ω : Ω} (hD : Dᴴ = D)
    (hc : Continuous fun t => G t ω)
    (hf : ∀ s, (G s ω).1ᴴ = (G s ω).1 ∧ (G s ω).2ᴴ = (G s ω).2) (i j : Fin (gramDim c))
    (t : ℝ≥0) :
    mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i t ω *
        mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) j t ω -
        ∫ s in Ioc (0 : ℝ) t, gramRealCov D0 D (toGramReal (G s.toNNReal ω)) i j =
      realCovL (qi i).2 (qi j).2 (gramCompensated D0 D G (qi i).1 t ω *
          gramCompensated D0 D G (qi j).1 t ω -
          ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D (qi i).1 (qi j).1 (G s.toNNReal ω)) +
        realCovL' (qi i).2 (qi j).2 (gramCompensated D0 D G (qi i).1 t ω *
          gramCompensated D0 D G (gramSwap (qi j).1) t ω -
          ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D (qi i).1 (gramSwap (qi j).1) (G s.toNNReal ω)) := by
  have i1 : Integrable (fun s : ℝ => gramCovEntry D0 D (qi i).1 (qi j).1 (G s.toNNReal ω))
      (volume.restrict (Ioc 0 t)) :=
    integrableOn_Ioc_of_continuous ((continuous_gramCovEntry D0 D _ _).comp hc) t
  have i2 : Integrable
      (fun s : ℝ => gramCovEntry D0 D (qi i).1 (gramSwap (qi j).1) (G s.toNNReal ω))
      (volume.restrict (Ioc 0 t)) :=
    integrableOn_Ioc_of_continuous ((continuous_gramCovEntry D0 D _ _).comp hc) t
  have hcov : ∀ s : ℝ, gramRealCov D0 D (toGramReal (G s.toNNReal ω)) i j =
      realCovL (qi i).2 (qi j).2 (gramCovEntry D0 D (qi i).1 (qi j).1 (G s.toNNReal ω)) +
        realCovL' (qi i).2 (qi j).2
          (gramCovEntry D0 D (qi i).1 (gramSwap (qi j).1) (G s.toNNReal ω)) := fun s => by
    simp only [gramRealCov, fromGramReal_toGramReal, realCovEntry_eq]
  simp only [hcov]
  rw [integral_add ((realCovL _ _).integrable_comp i1) ((realCovL' _ _).integrable_comp i2),
    (realCovL _ _).integral_comp_comm i1, (realCovL' _ _).integral_comp_comm i2,
    mpCompensated_gramReal hc i, mpCompensated_gramReal hc j, reImCLM_apply, reImCLM_apply,
    reIm_mul_reIm, star_gramCompensated hD hf, map_sub, map_sub]
  ring

/-- **The real coordinates of a Gram martingale-problem solution solve the real
martingale problem.** -/
theorem isMPSolutionOn_gramReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) :
    IsMPSolutionOn Q 𝓖 (gramRealDrift D0 D) (gramRealCov D0 D) univ
      (fun t ω => toGramReal (G t ω)) := by
  have hYm : ∀ t, Measurable[𝓖 t] (fun ω => toGramReal (G t ω)) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted t)).measurable
  have hρle : ∀ {W : Set (Fin (gramDim c) → ℝ)}, IsInteriorDomain W univ → ∀ {K : ℝ},
      (∀ H : Matrix c c ℂ × Matrix c c ℂ, toGramReal H ∈ W → (H.1.trace).re < K) →
      ∀ᵐ ω ∂Q, rawHit Wᶜ (fun t ω => toGramReal (G t ω)) ω ≤ gramTraceStop G K ω :=
    fun hW _ hK => by
      filter_upwards [hG.continuous] with ω hc
      rw [rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω)) hW.1.isClosed_compl
      (continuous_toGramReal.comp hc)]
      exact hitTime_le_gramTraceStop hK ω
  have hρeq : ∀ {W : Set (Fin (gramDim c) → ℝ)}, IsInteriorDomain W univ →
      ∀ᵐ ω ∂Q, exitTimeFrom W (fun t ω => toGramReal (G t ω)) ω =
        rawHit Wᶜ (fun t ω => toGramReal (G t ω)) ω := fun hW => by
    filter_upwards [hG.continuous] with ω hc
    rw [rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω)) hW.1.isClosed_compl
      (continuous_toGramReal.comp hc)]
    rfl
  have hherm : ∀ᵐ ω ∂Q, ∀ s, (G s ω).1ᴴ = (G s ω).1 ∧ (G s ω).2ᴴ = (G s ω).2 := by
    filter_upwards [hG.feasible] with ω h s
    exact herm_of_feasible (h s)
  refine ⟨fun t => continuous_toGramReal.comp_stronglyMeasurable (hG.adapted t), ?_, ?_, ?_⟩
  · filter_upwards [hG.continuous] with ω h
    exact continuous_toGramReal.comp h
  · intro W hW i
    obtain ⟨K, hK⟩ := exists_trace_level hW
    obtain ⟨N, hN, hNX⟩ := hG.drift K (qi i).1
    have hmod := hasMartingaleModification_stopped_of_clm hN hN hNX hNX (reImCLM (qi i).2) 0
      (X := mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i) (by
        filter_upwards [hG.continuous] with ω hc t
        rw [mpCompensated_gramReal hc i t, _root_.zero_apply, add_zero])
    refine exists_martingale_restrict hmod ?_ (isStoppingTime_rawHit hYm) (hρle hW hK)
      (hρeq hW)
    filter_upwards [hG.continuous] with ω hc
    exact continuous_mpCompensated_gramReal hc i
  · intro W hW i j
    obtain ⟨K, hK⟩ := exists_trace_level hW
    obtain ⟨N₁, hN₁, hN₁X⟩ := hG.bracket K (qi i).1 (qi j).1
    obtain ⟨N₂, hN₂, hN₂X⟩ := hG.bracket K (qi i).1 (gramSwap (qi j).1)
    have hmod := hasMartingaleModification_stopped_of_clm hN₁ hN₂ hN₁X hN₂X
      (realCovL (qi i).2 (qi j).2) (realCovL' (qi i).2 (qi j).2)
      (X := fun t ω =>
        mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) i t ω *
          mpCompensated (gramRealDrift D0 D) (fun t ω => toGramReal (G t ω)) j t ω -
          ∫ s in Ioc (0 : ℝ) t, gramRealCov D0 D (toGramReal (G s.toNNReal ω)) i j) (by
        filter_upwards [hG.continuous, hherm] with ω hc hf t
        exact mpBracket_gramReal hD.1 hc hf i j t)
    refine exists_martingale_restrict hmod ?_ (isStoppingTime_rawHit hYm) (hρle hW hK)
      (hρeq hW)
    filter_upwards [hG.continuous] with ω hc
    refine ((continuous_mpCompensated_gramReal hc i).mul
      (continuous_mpCompensated_gramReal hc j)).sub ?_
    refine continuous_setIntegral_Ioc
      (g := fun u => gramRealCov D0 D (toGramReal (G u ω)) i j) fun t => ?_
    refine integrableOn_Ioc_of_continuous
      (g := fun u => gramRealCov D0 D (toGramReal (G u ω)) i j) ?_ t
    have : (fun u => gramRealCov D0 D (toGramReal (G u ω)) i j) = fun u =>
        realCovL (qi i).2 (qi j).2 (gramCovEntry D0 D (qi i).1 (qi j).1 (G u ω)) +
          realCovL' (qi i).2 (qi j).2 (gramCovEntry D0 D (qi i).1 (gramSwap (qi j).1) (G u ω)) := by
      funext u
      simp only [gramRealCov, fromGramReal_toGramReal, realCovEntry_eq]
    rw [this]
    exact ((realCovL _ _).continuous.comp ((continuous_gramCovEntry D0 D _ _).comp hc)).add
      ((realCovL' _ _).continuous.comp ((continuous_gramCovEntry D0 D _ _).comp hc))

end BlockBand.SourceProcess.Stochastic.GramUniqueness
