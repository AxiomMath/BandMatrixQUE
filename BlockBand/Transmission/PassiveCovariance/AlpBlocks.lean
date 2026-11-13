module

public import BlockBand.Transmission.PassiveCovariance.GamNear

/-!
# Block forms of the weighted and unweighted expansions (tools for `alpFam`, `alpFamI`)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` (`Y ≻ 0`),
fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, word length `≤ L_w`, insertions `≤ K_d`; constants depend on
these only, uniformly in `W ≥ W₀`, in `X` and in the word. Operator norm.

With `σ₁(τ) = cτ₀ + bτ₁` (`sig1`) and `τ_j = (E⟨(𝒢α_j)_rr⟩)_r`:
* **`weightedBlock`**: `‖(K̂E[𝒢w])₀₀ - KM((Ew)₀₀ + Σ_j σ₁(τ_j)(Eγ_j)₀₀)‖ ≤ C/W²` (from
  `weightedExpansion`; the unbounded `X` never appears outside `K̂D⁻¹`);
* **`unweightedBlock`**: `‖(E[𝒢w])₀₀ - M((Ew)₀₀ + Σ_j σ₁(τ_j)(Eγ_j)₀₀)‖ ≤ C/W²` and
  `‖(E[𝒢w])₁₁ - v((Ew)₁₁ + Σ_j bτ_{j,0}(Eγ_j)₁₁)‖ ≤ C/W²` (from `unweightedExpansion`);
* `blkAt_bProj_mul`: `(P_pN)_rr = [r = p]N_rr`; `blkAt_sum`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `σ₁(τ) = cτ₀ + bτ₁`. -/
def sig1 (b : ℝ) (τ₀ τ₁ : ℂ) : ℂ := ((1 - 2 * b : ℝ) : ℂ) * τ₀ + (b : ℂ) * τ₁

/-- The block trace mean `E⟨F_rr⟩`. -/
abbrev trMean (b : ℝ) (F : LayerSample W .oneBlockOnePort → LayerMat W) (r : Fin 2) : ℂ :=
  ∫ ω, SourceMixing.blkTr (F ω) r ∂layerLaw W b .oneBlockOnePort

theorem blkAt_sum {ι : Type*} (t : Finset ι) (f : ι → LayerMat W) (r s : Fin 2) :
    blkAt (∑ j ∈ t, f j) r s = ∑ j ∈ t, blkAt (f j) r s := by
  ext x y; simp [blkAt, Matrix.sum_apply]

theorem blkAt_bProj (p r t : Fin 2) :
    blkAt (bProj p : LayerMat W) r t = if r = t ∧ r = p then 1 else 0 := by
  fin_cases p <;> fin_cases r <;> fin_cases t <;> ext x y <;>
    simp [blkAt, siteOf, bProj, bInd, blkOf, Matrix.diagonal_apply, Matrix.one_apply]

/-- `(P_pN)_rs = [r = p]N_rs`. -/
theorem blkAt_bProj_mul (p r s : Fin 2) (N : LayerMat W) :
    blkAt (bProj p * N) r s = (if r = p then (1 : ℂ) else 0) • blkAt N r s := by
  rw [blkAt_mul, Fin.sum_univ_two, blkAt_bProj, blkAt_bProj]
  fin_cases p <;> fin_cases r <;> simp

/-- `(K̂D⁻¹N)₀₀ = KM·N₀₀`. -/
theorem blkAt_kHatInv_mul {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hW : 1 ≤ W)
    (hD : IsUnit (dressed b E X)) (N : LayerMat W) :
    blkAt (kHat b E X * (dressed b E X)⁻¹ * N) 0 0 = SourceMixing.kmOf b E X * blkAt N 0 0 := by
  have h01 := kHat_mbar_blk b E X hW hD
  have e : mbarSide b E X false = (dressed b E X)⁻¹ := rfl
  rw [e] at h01
  rw [blkAt_mul, Fin.sum_univ_two, h01, Matrix.zero_mul, add_zero]; rfl

/-- **The weighted expansion, physical block.** -/
theorem weightedBlock (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 -
          SourceMixing.kmOf b E X *
            (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 +
            ∑ j, sig1 b
                (trMean b (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0)
                (trMean b (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := SourceMixing.weightedExpansion hA hb0 hb h1 h2 Lw Kd
  obtain ⟨CK, WK, hCK, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  refine ⟨C, max (max W₁ WK) 1, hC, fun W hW X hX ℓ hℓ wd D hD => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWK⟩, hW1⟩ := hW
  obtain ⟨hU, -, -, -⟩ := hK W hWK X hX
  have h := (norm_blkAt_le _ 0 0).trans (hw W hW₁ X hX ℓ hℓ wd D hD)
  rw [blkAt_sub, blkAt_kHatInv_mul hW1 hU, blkAt_add, blkAt_sum] at h
  simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).1] at h
  exact h

/-- **The unweighted expansion, both diagonal blocks.** -/
theorem unweightedBlock (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 -
          SourceMixing.mOf b E X *
            (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 +
            ∑ j, sig1 b
                (trMean b (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0)
                (trMean b (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D)) 1 1 -
          SourceMixing.vOf b E X •
            (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 1 1 +
            ∑ j, ((b : ℂ) *
                trMean b (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 1 1)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hu⟩ := SourceMixing.unweightedExpansion hA hb0 hb h1 h2 Lw Kd
  obtain ⟨CD, WD, hCD, hDB⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  refine ⟨C, max W₁ WD, hC, fun W hW X hX ℓ hℓ wd D hD => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨-, -, -, -, bl0, bl1, -⟩ := hDB W hW.2 X hX
  have h := hu W hW.1 X hX ℓ hℓ wd D hD
  constructor
  · have h0 := (norm_blkAt_le _ 0 0).trans h
    rw [blkAt_sub, bl0, blkAt_add, blkAt_sum] at h0
    simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).1] at h0
    exact h0
  · have h1' := (norm_blkAt_le _ 1 1).trans h
    rw [blkAt_sub, bl1, blkAt_add, blkAt_sum] at h1'
    simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).2] at h1'
    exact h1'

end BlockBand.Transmission.PassiveCovariance
