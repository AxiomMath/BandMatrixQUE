module

public import BlockBand.Transmission.PassiveCovariance.DressedTrace
public import BlockBand.Transmission.PassiveCovariance.TraceBilin
public import BlockBand.Transmission.PassiveCovariance.SdCentreProd
public import BlockBand.Transmission.PassiveCovariance.SdSite
public import BlockBand.Transmission.LengthUniform.BulkMeanExpansion
public import BlockBand.Transmission.LengthUniform.BulkReplica
public import BlockBand.Transmission.LengthUniform.BulkMeanFieldOp

/-!
# Bulk-uniform trace covariances and polynomial moments

Dressed trace–bilinear covariances, centring of dressed block traces, trace centring against
products of two dressed forms and the uniform mean bound, with constants and `W₀` uniform in
`E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Dressed trace–bilinear covariance**: `|Cov(W⁻¹Tr ℓ_k, u*w(𝒢)v)| ≤ (C/W²)‖u‖‖v‖`.
Bulk-uniform copy of `dressed_traceCov` (constants uniform on `bulkInterval κ`). -/
theorem dressed_traceCov_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ (k : Fin 6)
      (u v : LayerSite W .oneBlockOnePort → ℂ),
        Integrable (trLetter b E X k) (layerLaw W b .oneBlockOnePort) ∧
        Integrable (fun ω => wordForm (kHat b E X) u v wd D (gRes b E X ω))
          (layerLaw W b .oneBlockOnePort) ∧
        Integrable (fun ω => trLetter b E X k ω * wordForm (kHat b E X) u v wd D (gRes b E X ω))
          (layerLaw W b .oneBlockOnePort) ∧
        ‖(∫ ω, trLetter b E X k ω * wordForm (kHat b E X) u v wd D (gRes b E X ω)
            ∂layerLaw W b .oneBlockOnePort) -
          (∫ ω, trLetter b E X k ω ∂layerLaw W b .oneBlockOnePort) *
            ∫ ω, wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm u * vecNorm v) := by
  obtain ⟨C₀, W₀, h⟩ := hA.traceMatrix b hb0 hb κ hκ (max Lw 1) (max Kd 1)
  refine ⟨4 ^ (Lw + 1) * max C₀ 0, W₀, by positivity, fun W hW E hEκ X hX ℓ hℓ wd D hD k u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  set μ := layerLaw W b .oneBlockOnePort
  set f := trLetter b E X k
  have hD1 : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ max Kd 1 :=
    fun _ => norm_one_matrix_le.trans (le_max_right _ _)
  -- the passive pieces
  set g : Fin 2 × Fin 2 × (Fin ℓ → Fin 2 × Fin 2) → LayerSample W .oneBlockOnePort → ℂ :=
    fun i ω => bilinear (u ∘ siteOf i.1) (passiveWord E (boundaryZ b E) X (pathWd wd i.2.2)
      (pathD ℓ D i.1 i.2.1 i.2.2) ω) (v ∘ siteOf i.2.1)
  have hdec : ∀ ω, wordForm (kHat b E X) u v wd D (gRes b E X ω) = ∑ i, g i ω := by
    intro ω
    rw [wordForm, wordForm_blocks, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [blkAt_wordVal]
    simp only [g, bilinear, sum_mulVec, dotProduct_sum]
  have hpc : ∀ i : Fin 2 × Fin 2 × (Fin ℓ → Fin 2 × Fin 2),
      Integrable f μ ∧
      (∀ x y, Integrable (fun ω => passiveWord E (boundaryZ b E) X (pathWd wd i.2.2)
        (pathD ℓ D i.1 i.2.1 i.2.2) ω x y) μ) ∧
      (∀ x y, Integrable (fun ω => f ω * passiveWord E (boundaryZ b E) X (pathWd wd i.2.2)
        (pathD ℓ D i.1 i.2.1 i.2.2) ω x y) μ) ∧
      ‖covMat μ f (passiveWord E (boundaryZ b E) X (pathWd wd i.2.2) (pathD ℓ D i.1 i.2.1 i.2.2))‖ ≤
        C₀ / (W : ℝ) ^ 2 := by
    intro i
    obtain ⟨hf, hU, hfU, hcov⟩ := h W hW E hEκ _
      (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX 1 ℓ (le_max_right _ _)
      (hℓ.trans (le_max_left _ _)) (fun _ => (k, false)) (fun _ => 1) (pathWd wd i.2.2)
      (pathD ℓ D i.1 i.2.1 i.2.2) hD1
      (fun j => (norm_pathD_le ℓ D hD _ _ _ j).trans (le_max_left _ _))
    simp only [passiveWord_single_fun] at hf hfU hcov
    exact ⟨hf, hU, hfU, hcov⟩
  have hgi : ∀ i, Integrable (g i) μ := fun i =>
    integrable_bilinear _ (hpc i).2.1 _ _
  have hfgi : ∀ i, Integrable (fun ω => f ω * g i ω) μ := fun i => by
    have := integrable_bilinear (μ := μ) (fun ω => f ω • passiveWord E (boundaryZ b E) X
      (pathWd wd i.2.2) (pathD ℓ D i.1 i.2.1 i.2.2) ω) (hpc i).2.2.1 (u ∘ siteOf i.1) (v ∘ siteOf i.2.1)
    simpa only [bilinear_smul] using this
  have hpiece : ∀ i, (∫ ω, f ω * g i ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g i ω ∂μ =
      bilinear (u ∘ siteOf i.1) (covMat μ f (passiveWord E (boundaryZ b E) X (pathWd wd i.2.2)
        (pathD ℓ D i.1 i.2.1 i.2.2))) (v ∘ siteOf i.2.1) := fun i => by
    rw [covMat, bilinear_sub, bilinear_smul, bilinear_matrixExpect (fun ω => f ω •
      passiveWord E (boundaryZ b E) X (pathWd wd i.2.2) (pathD ℓ D i.1 i.2.1 i.2.2) ω) _ _
      (hpc i).2.2.1, bilinear_matrixExpect _ _ _ (hpc i).2.1]
    simp only [bilinear_smul, g]
  have hΨ : Integrable (fun ω => wordForm (kHat b E X) u v wd D (gRes b E X ω)) μ := by
    simp only [hdec]; exact integrable_finsetSum _ fun i _ => hgi i
  have hfΨ : Integrable (fun ω => f ω * wordForm (kHat b E X) u v wd D (gRes b E X ω)) μ := by
    simp only [hdec, Finset.mul_sum]; exact integrable_finsetSum _ fun i _ => hfgi i
  refine ⟨(hpc ((0, 0, fun _ => (0, 0)))).1, hΨ, hfΨ, ?_⟩
  have hsum : (∫ ω, f ω * wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂μ) -
      (∫ ω, f ω ∂μ) * ∫ ω, wordForm (kHat b E X) u v wd D (gRes b E X ω) ∂μ =
      ∑ i, ((∫ ω, f ω * g i ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g i ω ∂μ) := by
    simp only [hdec, Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hfgi i, integral_finsetSum _ fun i _ => hgi i,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsum]
  have hC : 0 ≤ max C₀ 0 / (W : ℝ) ^ 2 := by positivity
  calc ‖∑ i, ((∫ ω, f ω * g i ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g i ω ∂μ)‖
      ≤ ∑ _i : Fin 2 × Fin 2 × (Fin ℓ → Fin 2 × Fin 2),
          max C₀ 0 / (W : ℝ) ^ 2 * (vecNorm u * vecNorm v) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [hpiece]
        refine (norm_bilinear_le _ _ _).trans ?_
        have hu := vecNorm_comp_le u (siteOf_injective (W := W) i.1)
        have hv := vecNorm_comp_le v (siteOf_injective (W := W) i.2.1)
        have hc := (hpc i).2.2.2.trans (div_le_div_of_nonneg_right (le_max_left C₀ 0) (by positivity))
        calc vecNorm (u ∘ siteOf i.1) * ‖covMat μ f (passiveWord E (boundaryZ b E) X
              (pathWd wd i.2.2) (pathD ℓ D i.1 i.2.1 i.2.2))‖ * vecNorm (v ∘ siteOf i.2.1)
            ≤ vecNorm u * (max C₀ 0 / (W : ℝ) ^ 2) * vecNorm v :=
              mul_le_mul (mul_le_mul hu hc (norm_nonneg _) (vecNorm_nonneg _)) hv
                (vecNorm_nonneg _) (mul_nonneg (vecNorm_nonneg _) hC)
          _ = _ := by ring
    _ = (4 : ℝ) ^ (ℓ + 1) * (max C₀ 0 / (W : ℝ) ^ 2 * (vecNorm u * vecNorm v)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
        push_cast; ring
    _ ≤ (4 : ℝ) ^ (Lw + 1) * (max C₀ 0 / (W : ℝ) ^ 2 * (vecNorm u * vecNorm v)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
          (mul_nonneg hC (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)))
    _ = _ := by ring

/-- **Centring of a dressed block trace** against a dressed form (from `wordTraceCov`).
Bulk-uniform copy of `layerTrace_dressedCov` (constants uniform on `bulkInterval κ`). -/
theorem layerTrace_dressedCov_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₀, hC, h⟩ := wordTraceCov_bulk hA hb0 hb hκ Lw Kd
  refine ⟨C, W₀, hC, fun W hW E hEκ X hX ℓ hℓ wd D hD ℓ' hℓ' wd' D' hD' q u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hf, hU, hfU, hcov⟩ := h W hW E hEκ X hX ℓ' hℓ' wd' D' hD' ℓ hℓ wd D hD q
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

/-- **Trace centring against a product of two dressed forms.**
Bulk-uniform copy of `layerTrace_cov_prod` (constants uniform on `bulkInterval κ`). -/
theorem layerTrace_cov_prod_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₀, hC, h⟩ := layerTrace_dressedCov_bulk hA hb0 hb hκ (2 * Lw) (max Kd 1 ^ 2)
  obtain ⟨C', W₁, -, hdt⟩ := dressed_traceCov_bulk hA hb0 hb hκ (2 * Lw) (max Kd 1 ^ 2)
  refine ⟨C, max W₀ W₁, hC,
    fun W hW E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ ℓ' hℓ' wd' D' hD' q
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
  obtain ⟨-, -, hτF, hb'⟩ := h W (le_trans (le_max_left _ _) hW) E hEκ X hX (ℓ₂ + ℓ₁) (by omega) (catWd wd₂ ℓ₁ wd₁) _ hcat ℓ' (by omega) wd' D'
    (fun j => ((hD' j).trans (le_max_left _ _)).trans hKK) q u₁ v₂
  have hF : Integrable (fun ω => wordForm (kHat b E X) u₁ v₂ (catWd wd₂ ℓ₁ wd₁)
      (catD (vecMulVec v₁ (star u₂)) D₂ ℓ₁ D₁) (gRes b E X ω)) (layerLaw W b .oneBlockOnePort) := by
    exact (hdt W (le_trans (le_max_right _ _) hW) E hEκ X hX (ℓ₂ + ℓ₁) (by omega) (catWd wd₂ ℓ₁ wd₁) _ hcat 0 u₁ v₂).2.1
  simp only [e]
  exact ⟨hF, hτF, hb'⟩

/-- **Uniform mean bound** for polynomially bounded functionals: `|E F| ≤ K·C` when
`|F| ≤ K(1+B)^k`, `k ≤ R`, uniformly over passive inputs.
Bulk-uniform copy of `norm_integral_poly_le` (constants uniform on `bulkInterval κ`). -/
theorem norm_integral_poly_le_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (R : ℕ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (F : LayerSample W .oneBlockOnePort → ℂ) (K : ℝ) (k : ℕ), k ≤ R →
      (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k) →
        ‖∫ ω, F ω ∂layerLaw W b .oneBlockOnePort‖ ≤ K * C := by
  obtain ⟨C₀, W₀, hC₀, hm⟩ := btFun_moment_bulk hA hb0 hb hκ (2 * ((R + 1 : ℕ) : ℝ)) (by
    have : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos R
    linarith)
  refine ⟨(C₀ ^ (R + 1)) ^ 2, W₀, by positivity, fun W hW E hEκ X hX F K k hk hF => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  set μ := layerLaw W b .oneBlockOnePort
  set g : LayerSample W .oneBlockOnePort → ℝ := fun ω => (1 + btFun b E X ω) ^ (R + 1)
  have hB1 : ∀ ω, 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X
  have hgm : AEStronglyMeasurable (fun ω => 1 + btFun b E X ω) μ :=
    (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable
  have hg2 := eLpNorm_pow_le (μ := μ) (fun ω => (zero_le_one.trans (hB1 ω))) hgm (R + 1)
    (Nat.succ_pos R) (hm W hW E hEκ X hX)
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

/-- `memLp_two_of_poly` for every exponent `k ≤ R` and every sign of the constant.
Bulk-uniform copy of `memLp_poly` (constants uniform on `bulkInterval κ`). -/
theorem memLp_poly_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (R : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ (K : ℝ) (k : ℕ), k ≤ R → (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k) →
        MemLp F 2 (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hm⟩ := memLp_two_of_poly_bulk hA hb0 hb hκ (R + 1) (by omega)
  refine ⟨W₀, fun W hW E hEκ X hX F hF K k hk hK => hm W hW E hEκ X hX F hF (max K 0) fun ω => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have h1' : 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X ω
  have hp : (1 + btFun b E X ω) ^ k ≤ (1 + btFun b E X ω) ^ (R + 1) :=
    pow_le_pow_right₀ h1' (by omega)
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ k := by positivity
  calc ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k := hK ω
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ (R + 1) :=
        mul_le_mul_of_nonneg_left hp (le_max_right _ _)

end BlockBand.Transmission.CovarianceBulk
