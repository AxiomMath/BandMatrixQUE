module

public import BlockBand.Transmission.SourceMixing.WordMean
public import BlockBand.Transmission.LengthUniform.BulkMeanExpansion

/-!
# Bulk-uniform bounded means of dressed words

Means of dressed words are bounded uniformly over passive inputs and over
`E ∈ bulkInterval κ` (`wordMean_bound_bulk`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Bounded means of dressed words**, uniformly over passive inputs.
Bulk-uniform copy of `wordMean_bound`: constants uniform over `E ∈ bulkInterval κ`. -/
theorem wordMean_bound_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
        (∀ α β, Integrable (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        Integrable (fun ω => ‖wordVal (kHat b E X) (gRes b E X ω) wd D‖)
          (layerLaw W b .oneBlockOnePort) ∧
        ∫ ω, ‖wordVal (kHat b E X) (gRes b E X ω) wd D‖ ∂layerLaw W b .oneBlockOnePort ≤ C ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort)
          (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)‖ ≤ C ∧
        ∀ r : Fin 2, ‖∫ ω, blkTr (wordVal (kHat b E X) (gRes b E X ω) wd D) r
          ∂layerLaw W b .oneBlockOnePort‖ ≤ C := by
  obtain ⟨Cb, Wb, hCb, hm⟩ := btFun_moment_bulk hA hb0 hb hκ (2 * ((Lw + 1 : ℕ) : ℝ)) (by
    have : (1 : ℝ) ≤ ((Lw + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 Lw
    linarith)
  obtain ⟨_, Wt, _, htc⟩ := wordTraceCov_bulk hA hb0 hb hκ Lw Kd
  set K₁ := max (max Kd 0) 1 ^ (Lw + 1)
  have hK₁ : 0 ≤ K₁ := by positivity
  set C := K₁ * (Cb ^ (Lw + 1)) ^ 2
  refine ⟨C, max Wb Wt, by positivity, fun W hW E hE X hX ℓ hℓ wd D hD => ?_⟩
  set μ := layerLaw W b .oneBlockOnePort
  set g : LayerSample W .oneBlockOnePort → ℝ := fun ω => (1 + btFun b E X ω) ^ (Lw + 1)
  have hg1 : ∀ ω, 1 ≤ g ω := fun ω => one_le_pow₀ (one_le_one_add_btFun b E X ω)
  have hgm : Measurable g := (measurable_const.add (measurable_btFun b E X)).pow_const _
  have hgL : eLpNorm g 2 μ ≤ ENNReal.ofReal (Cb ^ (Lw + 1)) := by
    have h := eLpNorm_pow_le (μ := μ) (g := fun ω => 1 + btFun b E X ω)
      (fun ω => by have := btFun_nonneg b E X ω; positivity)
      (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable (Lw + 1)
      (by omega) (hm W (le_trans (le_max_left _ _) hW) E hE X hX)
    rw [ENNReal.ofReal_pow hCb]; exact h
  have hgM : MemLp g 2 μ := lt_of_le_of_lt hgL ENNReal.ofReal_lt_top
  have hgi : Integrable g μ := hgM.integrable one_le_two
  have hg2i : Integrable (fun ω => g ω ^ 2) μ := hgM.integrable_sq
  have hgint : ∫ ω, g ω ∂μ ≤ (Cb ^ (Lw + 1)) ^ 2 := by
    refine (integral_mono hgi hg2i fun ω => ?_).trans
      (integral_sq_le_of_eLpNorm hgm.aestronglyMeasurable (by positivity) hgL)
    have := hg1 ω; nlinarith
  have hpt := fun ω => norm_wordVal_le_poly b E X Kd hℓ wd D hD ω
  have hni : Integrable (fun ω => ‖wordVal (kHat b E X) (gRes b E X ω) wd D‖) μ :=
    (hgi.const_mul K₁).mono' (measurable_norm_wordVal b E X wd D).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt ω)
  have hnint : ∫ ω, ‖wordVal (kHat b E X) (gRes b E X ω) wd D‖ ∂μ ≤ C := by
    calc _ ≤ ∫ ω, K₁ * g ω ∂μ := integral_mono hni (hgi.const_mul K₁) hpt
      _ = K₁ * ∫ ω, g ω ∂μ := integral_const_mul _ _
      _ ≤ C := mul_le_mul_of_nonneg_left hgint hK₁
  have hent := (htc W (le_trans (le_max_right _ _) hW) E hE X hX ℓ hℓ wd D hD ℓ hℓ wd D hD 0).2.1
  have hmat : ‖matrixExpect μ (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)‖ ≤ C :=
    (norm_matrixExpect_le _ hent hni).trans hnint
  refine ⟨hent, hni, hnint, hmat, fun r => ?_⟩
  rw [integral_blkTr _ hent]
  exact (norm_blkTr_le _ _).trans hmat

end BlockBand.Transmission.LengthUniform
