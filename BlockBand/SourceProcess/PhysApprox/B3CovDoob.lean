module

public import BlockBand.SourceProcess.PhysApprox.B3GramSum

/-!
# The centred covariances from the raw brackets

The Doob bound of the generator estimates bounds the raw bracket error by the
centred-covariance error plus the two mean squares. This file proves the reverse inequality. By the
Doob identity `E_j[(F - E_jF)(G - E_jG)] = E_j[FG] - E_jF E_jG`, the centred error is at most the
raw error plus `∫‖E_jF‖² + ∫‖E_jG‖²`:

* `cov_lintegral_centred_le` (generic, `L²`);
* `genCovStep_le_br`, `genConjCovStep_le_conj`: the same for the closed process;
* `kStepCov_of_bracket`, `kStepConjCov_of_conj`, `gramSumStepCov_of_bracket`: the centred estimates
  `KStepCov`, `KStepConjCov`, `GramSumStepCov` follow from the raw estimates `KStepBracket`,
  `KStepConj`, `GramSumStepBracket` together with the `L²` estimates (`GenStepMemL2`,
  `GenStepMeanL2`, or their Gram parts).

So, modulo the `L²` estimates, each centred estimate is equivalent to its raw estimate. The raw
form is the one that `ContractingWords.LayerCov` controls.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Generic reverse Doob bound
-/

section Generic

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The centred-covariance error is at most the raw error plus the two mean squares.** -/
theorem cov_lintegral_centred_le [IsFiniteMeasure μ] (hm : m ≤ m0) (A : Set Ω) {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (κ : Ω → ℂ) :
    ∫⁻ y, ‖A.indicator (fun y =>
        μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) y‖ₑ ∂μ ≤
      ∫⁻ y, ‖A.indicator (fun y => μ[F * G | m] y - κ y) y‖ₑ ∂μ +
        (∫⁻ y, ‖μ[F | m] y‖ₑ ^ 2 ∂μ + ∫⁻ y, ‖μ[G | m] y‖ₑ ^ 2 ∂μ) := by
  have hae := gen_condExp_mul_eq_centred hm hF hG
  have hma : Measurable fun y => ‖μ[F | m] y‖ₑ ^ 2 :=
    ((stronglyMeasurable_condExp.mono hm).measurable.enorm).pow_const 2
  have hmc : Measurable fun y => ‖μ[G | m] y‖ₑ ^ 2 :=
    ((stronglyMeasurable_condExp.mono hm).measurable.enorm).pow_const 2
  calc ∫⁻ y, ‖A.indicator (fun y =>
        μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) y‖ₑ ∂μ
      ≤ ∫⁻ y, (‖A.indicator (fun y => μ[F * G | m] y - κ y) y‖ₑ +
          (‖μ[F | m] y‖ₑ ^ 2 + ‖μ[G | m] y‖ₑ ^ 2)) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        by_cases hyA : y ∈ A
        · simp only [Set.indicator_of_mem hyA]
          rw [hy]
          simp only [Pi.add_apply, Pi.mul_apply]
          calc ‖μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y‖ₑ
              = ‖(μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y + μ[F | m] y * μ[G | m] y -
                  κ y) + -(μ[F | m] y * μ[G | m] y)‖ₑ := by ring_nf
            _ ≤ ‖μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y + μ[F | m] y * μ[G | m] y - κ y‖ₑ +
                  ‖-(μ[F | m] y * μ[G | m] y)‖ₑ := enorm_add_le _ _
            _ ≤ _ := by
                gcongr
                rw [enorm_neg, enorm_mul]
                exact gen_mul_le_sq_add_sq _ _
        · simp only [Set.indicator_of_notMem hyA, enorm_zero, zero_add]
          exact bot_le
    _ = ∫⁻ y, ‖A.indicator (fun y => μ[F * G | m] y - κ y) y‖ₑ ∂μ +
          ∫⁻ y, (‖μ[F | m] y‖ₑ ^ 2 + ‖μ[G | m] y‖ₑ ^ 2) ∂μ :=
        lintegral_add_right' _ (hma.add hmc).aemeasurable
    _ = _ := by
        congr 1
        exact lintegral_add_left hma _

end Generic

/-!
## The closed process
-/

/-- **Closed centred covariance ≤ raw bracket + mean squares.** -/
theorem genCovStep_le_br (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np)
    (hF : MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c)) 2
      (closedLaw b W np))
    (hG : MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c')) 2
      (closedLaw b W np)) :
    genCovStep b E s h τ m R W j Vs c c' ≤
      genBrStep b E s h τ m R W j Vs c c' +
        (genMeanSq b E s h τ m R W j Vs c + genMeanSq b E s h τ m R W j Vs c') := by
  unfold genBrStep genCovStep genMeanSq
  rw [Set.indicator_mul]
  exact cov_lintegral_centred_le (gen_sigma_le W j np) _ hF hG _

/-- **Closed centred conjugate covariance ≤ raw conjugate bracket + mean squares.** -/
theorem genConjCovStep_le_conj (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np)
    (hF : MemLp ((b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np))) 2 (closedLaw b W np))
    (hG : MemLp ((b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np))) 2 (closedLaw b W np)) :
    genConjCovStep (K := K) b E s h τ m R W j Vs ij kl ≤
      genConjStep (K := K) b E s h τ m R W j Vs ij kl +
        (genMeanSq b E s h τ m R W j Vs (Sum.inr ij : CIdx K np) +
          genMeanSq b E s h τ m R W j Vs (Sum.inr kl : CIdx K np)) := by
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  set g := b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np)
  have hconj : A.indicator (fun y => conj (g y)) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ A.indicator g := by
    funext y
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hG' : MemLp (A.indicator (fun y => conj (g y))) 2 μ := by
    rw [hconj]; exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hG
  have hmean : ∫⁻ y, ‖μ[A.indicator (fun y => conj (g y)) | b3Sigma W j np] y‖ₑ ^ 2 ∂μ =
      ∫⁻ y, ‖μ[A.indicator g | b3Sigma W j np] y‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm (m := b3Sigma W j np)
      (hG.integrable (by norm_num)) (μ := μ)
    rw [hconj]
    filter_upwards [h] with y hy
    rw [← hy]
    simp
  have key := cov_lintegral_centred_le (gen_sigma_le W j np) A hF hG'
    (fun y => (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y))
  unfold genConjStep genConjCovStep genMeanSq
  rw [Set.indicator_mul]
  rw [hmean] at key
  exact key

/-!
## The centred estimates from the raw estimates and the `L²` estimates
-/

/-- **`GenStepMemL2 + GenStepMeanL2 + KStepBracket ⇒ KStepCov`.** -/
theorem kStepCov_of_bracket (hL : GenStepMemL2) (hM : GenStepMeanL2) (hB : KStepBracket) :
    KStepCov := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevB⟩ := hB b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevB, eventually_ge_atTop 1]
    with W hWL hWM hWB hW1 j hj ij c'
  exact (genCovStep_le_br b E s h τ m R W j (Vs W) _ c' (hWL j hj _) (hWL j hj c')).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWB j hj ij c') (hWM j hj _) (hWM j hj c'))

/-- **`GenStepMemL2 + GenStepMeanL2 + KStepConj ⇒ KStepConjCov`.** -/
theorem kStepConjCov_of_conj (hL : GenStepMemL2) (hM : GenStepMeanL2) (hB : KStepConj) :
    KStepConjCov := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevB⟩ := hB b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevB, eventually_ge_atTop 1]
    with W hWL hWM hWB hW1 j hj ij kl
  exact (genConjCovStep_le_conj b E s h τ m R W j (Vs W) ij kl (hWL j hj _)
    (hWL j hj _)).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWB j hj ij kl) (hWM j hj _) (hWM j hj _))

/-- **`GramSumStepMemL2 + GramSumStepMeanL2 + GramSumStepBracket ⇒ GramSumStepCov`.** -/
theorem gramSumStepCov_of_bracket (hL : GramSumStepMemL2) (hM : GramSumStepMeanL2)
    (hB : GramSumStepBracket) : GramSumStepCov := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevB⟩ := hB b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevB, eventually_ge_atTop 1]
    with W hWL hWM hWB hW1 j hj e e'
  exact (genCovStep_le_br b E s h τ m R W j (Vs W) _ _ (hWL j hj e) (hWL j hj e')).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWB j hj e e') (hWM j hj e) (hWM j hj e'))

end BlockBand.SourceProcess.PhysApprox.B3
