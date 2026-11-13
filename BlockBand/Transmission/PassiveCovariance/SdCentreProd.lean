module

public import BlockBand.Transmission.PassiveCovariance.SdCentre

/-!
# Trace centring against a product of two dressed forms; the uniform mean bound

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`, passive `X`;
`b, E, L_w, K_d` are fixed first, then `C, W₀`.

* `layerTrace_cov_prod`: `F = u₁*w₁v₁`, `Q = u₂*w₂v₂`, `‖v₁‖‖u₂‖ ≤ 1`, `τ = W⁻¹Tr blk_{qq}(w'(𝒢))`:
  `|E[τFQ] - Eτ·E[FQ]| ≤ (C/W²)‖u₁‖‖v₂‖` (`FQ` is one dressed form of length `≤ 2L_w` with
  insertions `≤ max(K_d,1)²`, `WordCat`).
* `norm_integral_poly_le`: `|E F| ≤ K·C` for `|F| ≤ K(1 + B)^k`, `k ≤ R`, uniformly over passive
  inputs (the `moments` clause of `PassiveBoundsStatement` via `btFun_moment`); it gives
  `|E[u*w(𝒢)v]| ≤ C‖u‖‖v‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Trace centring against a product of two dressed forms.** -/
theorem layerTrace_cov_prod (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → LayerMat W), (∀ j, ‖D₁ j‖ ≤ Kd) →
      ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw → ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ ℓ' : ℕ, ℓ' ≤ Lw → ∀ (wd' : Fin ℓ' → Fin 4) (D' : Fin (ℓ' + 1) → LayerMat W), (∀ j, ‖D' j‖ ≤ Kd) →
      ∀ (q : Fin 2) (u₁ v₁ u₂ v₂ : LayerSite W .oneBlockOnePort → ℂ), vecNorm v₁ * vecNorm u₂ ≤ 1 →
        Integrable (fun ω => wordForm (kHat b E X) u₁ v₁ wd₁ D₁ (gRes b E X ω) *
          wordForm (kHat b E X) u₂ v₂ wd₂ D₂ (gRes b E X ω)) (layerLaw W b .oneBlockOnePort) ∧
        Integrable (fun ω => (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace *
          (wordForm (kHat b E X) u₁ v₁ wd₁ D₁ (gRes b E X ω) *
            wordForm (kHat b E X) u₂ v₂ wd₂ D₂ (gRes b E X ω))) (layerLaw W b .oneBlockOnePort) ∧
        ‖(∫ ω, (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace *
            (wordForm (kHat b E X) u₁ v₁ wd₁ D₁ (gRes b E X ω) *
              wordForm (kHat b E X) u₂ v₂ wd₂ D₂ (gRes b E X ω)) ∂layerLaw W b .oneBlockOnePort) -
          (∫ ω, (W : ℂ)⁻¹ * (blkAt (wordVal (kHat b E X) (gRes b E X ω) wd' D') q q).trace
            ∂layerLaw W b .oneBlockOnePort) *
            ∫ ω, wordForm (kHat b E X) u₁ v₁ wd₁ D₁ (gRes b E X ω) *
              wordForm (kHat b E X) u₂ v₂ wd₂ D₂ (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm u₁ * vecNorm v₂) := by
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov hA hb0 hb h1 h2 (2 * Lw) (max Kd 1 ^ 2)
  obtain ⟨C', W₁, -, hdt⟩ := dressed_traceCov hA hb0 hb h1 h2 (2 * Lw) (max Kd 1 ^ 2)
  refine ⟨C, max W₀ W₁, hC, fun W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD' q
    u₁ v₁ u₂ v₂ hn => ?_⟩
  have hK1 : 1 ≤ max Kd 1 := le_max_right _ _
  have hKK : max Kd 1 ≤ max Kd 1 ^ 2 := by nlinarith
  have hZ : ‖vecMulVec v₁ (star u₂)‖ ≤ 1 := (norm_vecMulVec_le v₁ u₂).trans hn
  have hcat := norm_catD_le hK1 _ hZ D₂ (fun j => (hD₂ j).trans (le_max_left _ _)) ℓ₁ D₁
    (fun j => (hD₁ j).trans (le_max_left _ _))
  have e : ∀ ω, wordForm (kHat b E X) u₁ v₁ wd₁ D₁ (gRes b E X ω) *
      wordForm (kHat b E X) u₂ v₂ wd₂ D₂ (gRes b E X ω) =
      wordForm (kHat b E X) u₁ v₂ (catWd wd₂ ℓ₁ wd₁) (catD (vecMulVec v₁ (star u₂)) D₂ ℓ₁ D₁)
        (gRes b E X ω) := fun ω => wordForm_mul_wordForm _ _ _ _ _ _ _ _ _ _
  obtain ⟨-, -, hτF, hb'⟩ := h W (le_trans (le_max_left _ _) hW) X hX (ℓ₂ + ℓ₁) (by omega) (catWd wd₂ ℓ₁ wd₁) _ hcat ℓ' (by omega) wd' D'
    (fun j => ((hD' j).trans (le_max_left _ _)).trans hKK) q u₁ v₂
  have hF : Integrable (fun ω => wordForm (kHat b E X) u₁ v₂ (catWd wd₂ ℓ₁ wd₁)
      (catD (vecMulVec v₁ (star u₂)) D₂ ℓ₁ D₁) (gRes b E X ω)) (layerLaw W b .oneBlockOnePort) := by
    exact (hdt W (le_trans (le_max_right _ _) hW) X hX (ℓ₂ + ℓ₁) (by omega) (catWd wd₂ ℓ₁ wd₁) _ hcat 0 u₁ v₂).2.1
  simp only [e]
  exact ⟨hF, hτF, hb'⟩

/-- **Uniform mean bound** for polynomially bounded functionals: `|E F| ≤ K·C` when
`|F| ≤ K(1+B)^k`, `k ≤ R`, uniformly over passive inputs. -/
theorem norm_integral_poly_le (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (R : ℕ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (F : LayerSample W .oneBlockOnePort → ℂ) (K : ℝ) (k : ℕ), k ≤ R →
      (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k) →
        ‖∫ ω, F ω ∂layerLaw W b .oneBlockOnePort‖ ≤ K * C := by
  obtain ⟨C₀, W₀, hC₀, hm⟩ := btFun_moment hA hb0 hb h1 h2 (2 * ((R + 1 : ℕ) : ℝ)) (by
    have : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos R
    linarith)
  refine ⟨(C₀ ^ (R + 1)) ^ 2, W₀, by positivity, fun W hW X hX F K k hk hF => ?_⟩
  set μ := layerLaw W b .oneBlockOnePort
  set g : LayerSample W .oneBlockOnePort → ℝ := fun ω => (1 + btFun b E X ω) ^ (R + 1)
  have hB1 : ∀ ω, 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X
  have hgm : AEStronglyMeasurable (fun ω => 1 + btFun b E X ω) μ :=
    (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable
  have hg2 := eLpNorm_pow_le (μ := μ) (fun ω => (zero_le_one.trans (hB1 ω))) hgm (R + 1)
    (Nat.succ_pos R) (hm W hW X hX)
  rw [← ENNReal.ofReal_pow hC₀] at hg2
  have hgL : MemLp g 2 μ := lt_of_le_of_lt hg2 ENNReal.ofReal_lt_top
  have hsq := integral_sq_le_of_eLpNorm (hgm.pow _) (by positivity) hg2
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hF 0))
    (pow_pos (lt_of_lt_of_le zero_lt_one (hB1 0)) _)
  have hgi : Integrable g μ := hgL.integrable one_le_two
  have hg2i : Integrable (fun ω => g ω ^ 2) μ := hgL.integrable_sq
  have hle : ∀ ω, ‖F ω‖ ≤ K * g ω := fun ω => (hF ω).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB1 ω) (by omega)) hK)
  have hgg : ∫ ω, g ω ∂μ ≤ ∫ ω, g ω ^ 2 ∂μ := integral_mono hgi hg2i fun ω => by
    have : 1 ≤ g ω := one_le_pow₀ (hB1 ω)
    show g ω ≤ g ω ^ 2; nlinarith
  calc ‖∫ ω, F ω ∂μ‖ ≤ ∫ ω, ‖F ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, K * g ω ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
        (hgi.const_mul K) (Eventually.of_forall hle)
    _ = K * ∫ ω, g ω ∂μ := integral_const_mul _ _
    _ ≤ K * (C₀ ^ (R + 1)) ^ 2 := mul_le_mul_of_nonneg_left (hgg.trans hsq) hK

end BlockBand.Transmission.PassiveCovariance
