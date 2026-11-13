module

public import BlockBand.Transmission.PassiveCovariance.DressedBlocks

/-!
# Trace–bilinear covariances of dressed words are `O(W⁻²)`

Hypothesis `PassiveBoundsStatement` (only its `traceMatrix` clause). Law
`layerLaw W b .oneBlockOnePort`, passive `X` (`Y ⪰ 0`); `b, E`, the length `L_w` and the insertion
bound `K_d` are fixed first, then `C, W₀`.

The first input of the self-energy centring: for a dressed word `w`,
`|Cov(W⁻¹Tr ℓ_k, u*w(𝒢)v)| ≤ (C/W²)‖u‖‖v‖` (`dressed_traceCov`), by splitting the bilinear form
into its four blocks and each block into passive words.
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

theorem sum_layerSite_fin2 (g : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ γ, g γ = ∑ t : Fin 2, ∑ z, g (siteOf t z) := by
  rw [sum_layerSite, Fin.sum_univ_two]; rfl

/-- A layer bilinear form is the sum of the bilinear forms of its four blocks. -/
theorem wordForm_blocks (M : LayerMat W) (u v : LayerSite W .oneBlockOnePort → ℂ) :
    star u ⬝ᵥ (M *ᵥ v) =
      ∑ r : Fin 2, ∑ s : Fin 2, bilinear (u ∘ siteOf r) (blkAt M r s) (v ∘ siteOf s) := by
  have hrow : ∀ γ, (M *ᵥ v) γ = ∑ s : Fin 2, ∑ y, M γ (siteOf s y) * v (siteOf s y) := fun γ => by
    rw [mulVec, dotProduct, sum_layerSite_fin2]
  rw [dotProduct, sum_layerSite_fin2]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hrow]
  simp only [Finset.mul_sum, bilinear, dotProduct, mulVec, blkAt, Matrix.of_apply,
    Function.comp_apply, Pi.star_apply]
  rw [Finset.sum_comm]

theorem integrable_bilinear {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    (U : Ω → Matrix n n ℂ) (hU : ∀ x y, Integrable (fun ω => U ω x y) μ) (u v : n → ℂ) :
    Integrable (fun ω => bilinear u (U ω) v) μ := by
  simp only [bilinear, dotProduct, mulVec]
  exact integrable_finsetSum _ fun x _ =>
    (integrable_finsetSum _ fun y _ => (hU x y).mul_const _).const_mul _

/-- **Dressed trace–bilinear covariance**: `|Cov(W⁻¹Tr ℓ_k, u*w(𝒢)v)| ≤ (C/W²)‖u‖‖v‖`. -/
theorem dressed_traceCov (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C₀, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ (max Lw 1) (max Kd 1)
  refine ⟨4 ^ (Lw + 1) * max C₀ 0, W₀, by positivity, fun W hW X hX ℓ hℓ wd D hD k u v => ?_⟩
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
    obtain ⟨hf, hU, hfU, hcov⟩ := h W hW E (mem_bulkInterval_min E) _
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

end BlockBand.Transmission.PassiveCovariance
