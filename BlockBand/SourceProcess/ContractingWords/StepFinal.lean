module

public import BlockBand.SourceProcess.ContractingWords.LayerFreshMain
public import BlockBand.SourceProcess.ContractingWords.StepMeanMain
public import BlockBand.SourceProcess.ContractingWords.StepFluctMain

/-!
# `WordStepMean`, `WordStepFluct`: final assembly

`wordStepMean_of`, `wordStepFluct_of`: the one-step word bounds follow from the separator inputs.
They split into the contracting part (`SeparatorMeanUniform`, `SeparatorFluctUniform`, the
bulk-uniform complete-source-gap statements) and the ordinary part `σ ∈ {I, P}`, stated here:
* `SepMeanIdProj`: `‖E[NN*] - I‖`, `‖E[NPN*] - P‖ ≤ C(δ₀ + δ₁ + g/W + W⁻²)`. Proof: `NN* = I + 𝓔`
  and `FullSourceEstimates.mean` (`‖E𝓔‖ ≤ C(δ₀ + W⁻²)` on the bulk, `fullSourceEstimates_holds`);
  `NPN* = ι(LL*)ι*` (block form of `freshTransport`) and `ubarMean_bulk`
  (`‖E LL* - (1+αq/W)⁻¹‖ ≤ C(δ₀ + W⁻² + q/W)`), `g = 4ηq`.
* `SepFluctIdProj`: `‖u*(T - ET)v‖_Q ≤ C(W^{-1/2} + min(1,δ₀))‖u‖‖v‖` for `T = NN*, NPN*`.
  Proof: `FullSourceEstimates.fluct` on `δ₀ ≤ d₀`, the moment bound of `‖N‖` off it;
  `PassiveBoundsStatement.bilinear` for `U = LL*` (`uAt_boundaryZ`) and `NPN* = ι U ι*`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal Matrix.Norms.L2Operator

/-- **The means of the ordinary transported separators** `NN*`, `NPN*`. -/
def SepMeanIdProj : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 0 →
        let X := nearSchur (boundaryZ b E) XX
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ) - sepOf b E XX σ‖ ≤
          C * (jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W +
            ((W : ℝ)⁻¹) ^ 2)

/-- **Centered bilinear bounds of the ordinary transported separators.** -/
def SepFluctIdProj : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ Q : ℝ, 1 ≤ Q →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 0 → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal Q)
            (freshLaw W b) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W +
            min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX))) * vecNorm u * vecNorm v)

theorem gapFactor_ord {b E : ℝ} {s : ℂ} {σ : Separator} (h : σ.unconj + σ.conj = 0) :
    gapFactor b E s σ = 1 := by
  have h1 : σ.unconj = 0 := by omega
  have h2 : σ.conj = 0 := by omega
  rw [gapFactor, h1, h2, pow_zero, pow_zero, one_mul]

theorem separator_cases (σ : Separator) : σ.unconj + σ.conj = 0 ∨ σ.unconj + σ.conj = 1 := by
  cases σ <;> simp [Separator.unconj, Separator.conj]

theorem sepMeanAll_of (hS : SeparatorMeanUniform) (hI : SepMeanIdProj) : SepMeanAll := by
  intro b hb0 hb κ hκ
  obtain ⟨C₁, W₁, h₁⟩ := hS b hb0 hb κ hκ
  obtain ⟨C₂, W₂, hC₂, h₂⟩ := hI b hb0 hb κ hκ
  refine ⟨max C₁ 0 + C₂, max W₁ W₂, by positivity, fun W hW E hE s hs XX hXX σ => ?_⟩
  simp only [max_le_iff] at hW
  have hδ0 : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) XX) := by
    simp only [jetDistance0]; positivity
  have hδ1 : 0 ≤ jetDistance1 b E s (nearSchur (boundaryZ b E) XX) := by
    simp only [jetDistance1]; positivity
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := BlockBand.SourceProcess.FullSourceCovariance.conductance_nonneg b E hη.le
    (BlockBand.SourceProcess.FullSource.nearSchur_passive hη hXX)
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hR : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
      jetDistance1 b E s (nearSchur (boundaryZ b E) XX) +
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W +
      ((W : ℝ)⁻¹) ^ 2 := by positivity
  rcases separator_cases σ with h | h
  · have := h₂ W hW.2 E hE XX hXX σ h
    simp only [gapFactor_ord h, one_smul]
    refine this.trans ?_
    have hC : C₂ ≤ max C₁ 0 + C₂ := le_add_of_nonneg_left (le_max_right _ _)
    calc C₂ * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
          conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W +
            ((W : ℝ)⁻¹) ^ 2) ≤ C₂ * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
          jetDistance1 b E s (nearSchur (boundaryZ b E) XX) +
          conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W +
            ((W : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC₂
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hR
  · refine (h₁ W hW.1 E hE s hs XX hXX σ h).trans (mul_le_mul_of_nonneg_right ?_ hR)
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hC₂)

theorem sepFluctAll_of (hS : SeparatorFluctUniform) (hI : SepFluctIdProj) : SepFluctAll := by
  intro b hb0 hb κ hκ Q hQ
  obtain ⟨C₁, W₁, h₁⟩ := hS b hb0 hb κ hκ Q hQ
  obtain ⟨C₂, W₂, hC₂, h₂⟩ := hI b hb0 hb κ hκ Q hQ
  refine ⟨max C₁ 0 + C₂, max W₁ W₂, by positivity, fun W hW E hE XX hXX σ u v => ?_⟩
  simp only [max_le_iff] at hW
  have hm : 0 ≤ min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX)) :=
    le_min zero_le_one (by simp only [jetDistance0]; positivity)
  have hu := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u
  have hv := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v
  have hs : 0 ≤ 1 / Real.sqrt W := by positivity
  rcases separator_cases σ with h | h
  · refine (h₂ W hW.2 E hE XX hXX σ h u v).trans (ENNReal.ofReal_le_ofReal ?_)
    have hC : C₂ ≤ max C₁ 0 + C₂ := le_add_of_nonneg_left (le_max_right _ _)
    gcongr
  · refine (h₁ W hW.1 E hE XX hXX σ h u v).trans (ENNReal.ofReal_le_ofReal ?_)
    have hC : C₁ ≤ max C₁ 0 + C₂ := (le_max_left _ _).trans (le_add_of_nonneg_right hC₂)
    calc C₁ / Real.sqrt W * vecNorm u * vecNorm v ≤
        (max C₁ 0 + C₂) * (1 / Real.sqrt W) * vecNorm u * vecNorm v := by
          rw [div_eq_mul_one_div]; gcongr
      _ ≤ _ := by gcongr; linarith

/-- **`WordStepMean`** from the input hypotheses, the bulk-uniform separator bounds
`SeparatorMeanUniform`, `SeparatorFluctUniform` and the ordinary-separator bounds `SepMeanIdProj`,
`SepFluctIdProj`. -/
theorem wordStepMean_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hSep : SeparatorMeanUniform)
    (hSepF : SeparatorFluctUniform) (hIM : SepMeanIdProj) (hIF : SepFluctIdProj) :
    WordStepMean :=
  wordStepMean_of_layer hMT hGA hLp hSR
    (layerFreshBound_of hGA (sepMeanAll_of hSep hIM) (sepFluctAll_of hSepF hIF))

/-- **`WordStepFluct`** from the input hypotheses and the same four separator bounds. -/
theorem wordStepFluct_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hSep : SeparatorMeanUniform)
    (hSepF : SeparatorFluctUniform) (hIM : SepMeanIdProj) (hIF : SepFluctIdProj) :
    WordStepFluct :=
  wordStepFluct_of_layer hMT hGA hLp hSR
    (layerFreshBound_of hGA (sepMeanAll_of hSep hIM) (sepFluctAll_of hSepF hIF))

end BlockBand.SourceProcess.ContractingWords
