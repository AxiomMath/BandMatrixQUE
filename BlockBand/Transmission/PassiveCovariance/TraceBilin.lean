module

public import BlockBand.Transmission.PassiveCovariance.SdExpand
public import BlockBand.Transmission.SourceMixing.MeanExpansion

/-!
# Dressed block traces against dressed bilinear forms

Hypothesis `PassiveBoundsStatement`. A bilinear-form corollary of
`SourceMixing.wordTraceCov` (operator norm of the trace–word covariance matrix, multi-letter traces).

* `layerTrace_dressedCov`: `|E[τ·u*w(𝒢)v] - Eτ·E[u*w(𝒢)v]| ≤ (C/W²)‖u‖‖v‖` for
  `τ = W⁻¹Tr blk_{qq}(w'(𝒢))` (`= SourceMixing.blkTr`), uniformly in passive `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Centring of a dressed block trace** against a dressed form (from `wordTraceCov`). -/
theorem layerTrace_dressedCov (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ' : ℕ, ℓ' ≤ Lw →
      ∀ (wd' : Fin ℓ' → Fin 4) (D' : Fin (ℓ' + 1) → LayerMat W), (∀ j, ‖D' j‖ ≤ Kd) →
      ∀ (q : Fin 2) (u v : LayerSite W .oneBlockOnePort → ℂ),
        Integrable (fun ω => (W : ℂ)⁻¹ *
          (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace)
          (layerLaw W b .oneBlockOnePort) ∧
        Integrable (fun ω => wordForm (kHat b E X) u v wd D (gRes b E X ω))
          (layerLaw W b .oneBlockOnePort) ∧
        Integrable (fun ω => (W : ℂ)⁻¹ *
          (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace *
          wordForm (kHat b E X) u v wd D (gRes b E X ω)) (layerLaw W b .oneBlockOnePort) ∧
        ‖(∫ ω, (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace *
            wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort) -
          (∫ ω, (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace
            ∂layerLaw W b .oneBlockOnePort) *
            ∫ ω, wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm u * vecNorm v) := by
  obtain ⟨C, W₀, hC, h⟩ := SourceMixing.wordTraceCov hA hb0 hb h1 h2 Lw Kd
  refine ⟨C, W₀, hC, fun W hW X hX ℓ hℓ wd D hD ℓ' hℓ' wd' D' hD' q u v => ?_⟩
  obtain ⟨hf, hU, hfU, hcov⟩ := h W hW X hX ℓ' hℓ' wd' D' hD' ℓ hℓ wd D hD q
  set μ := layerLaw W b .oneBlockOnePort
  set f := fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) wd' D') q
  set U := fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D
  have hfU' : ∀ α β, Integrable (fun ω => (f ω • U ω) α β) μ := fun α β => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using hfU α β
  have e1 : ∫ ω, f ω * wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂μ =
      bilinear u (matrixExpect μ fun ω => f ω • U ω) v := by
    rw [bilinear_matrixExpect _ _ _ hfU']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [bilinear_smul]; rfl
  have e2 : ∫ ω, wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂μ = bilinear u (matrixExpect μ U) v := by
    rw [bilinear_matrixExpect _ _ _ hU]; rfl
  have hΨ : Integrable (fun ω => wordForm (kHat b E X) u v wd D (gRes b E X ω)) μ :=
    integrable_bilinear U hU u v
  refine ⟨hf, hΨ, ?_, ?_⟩
  · have h' := integrable_bilinear (μ := μ) (fun ω => f ω • U ω) hfU' u v
    simp only [bilinear_smul] at h'
    exact h'
  · change ‖(∫ ω, f ω * wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂μ) - (∫ ω, f ω ∂μ) * _‖ ≤ _
    rw [e1, e2, ← bilinear_smul, ← bilinear_sub]
    refine (norm_bilinear_le _ _ _).trans ?_
    calc vecNorm u * ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ *
          vecNorm v ≤ vecNorm u * (C / (W : ℝ) ^ 2) * vecNorm v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcov (vecNorm_nonneg _))
            (vecNorm_nonneg _)
      _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
