module

public import BlockBand.Transmission.SourceMixingBulk.MatchedScalars

/-!
# The three-resolvent weighted block, uniformly on the bulk

The estimate `threeBlock` with constants uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The three-resolvent weighted block.
The version of `threeBlock` with constants uniform on `bulkInterval κ`. -/
theorem threeBlock_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
            rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cw, Ww, hCw, hW3⟩ := weightedExpansion_bulk hA hb0 hb hκ 2 1
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨CN, WN, hCN, hN⟩ := mixedBlock_bulk hA hb0 hb hκ
  obtain ⟨Ct, Wt, hCt, hTh⟩ := scalarTheta_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cr, Wr, hCr, hRh⟩ := scalarRho_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨Cw + CK * (Ct * CN + Cr * CN), max (max (max Ww WK) (max WN Wt)) (max Wr WD),
    by positivity, fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWK⟩, hWN, hWt⟩, hWr, hWD⟩ := hW
  obtain ⟨-, -, hKD, -⟩ := hK W hWK E hE X hX
  obtain ⟨hN0, hKg⟩ := hN W hWN E hE X hX
  obtain ⟨-, hth, -, -, -⟩ := hTh W hWt E hE X hX
  obtain ⟨-, hrho, -, -, -⟩ := hRh W hWr E hE X hX
  obtain ⟨-, -, -, -, bl0, -, -, -, hG, -, -⟩ := hD W hWD E hE X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hT := hW3 W hWw E hE X hX 2 le_rfl wdR3 dR norm_dR_le
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdR3 dR) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_R3]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdR3 dR) =
      fun ω => SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_R3]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR3 dR 0) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r :=
    fun r => funext fun ω => by rw [wordAlpha_R30]
  have e4 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR3 dR 1) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))) r :=
    fun r => funext fun ω => by rw [wordAlpha_R31]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR3 dR 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_R30]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR3 dR 1) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_R31]
  rw [e1, e2, e3 0, e3 1, e4 0, e4 1, e5, e6] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r ∂μ) = tauTwo b E X r :=
    fun r => rfl
  have eu : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω *
      (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))) r ∂μ) = uTwo b E X r := fun r => rfl
  rw [et 0, et 1, eu 0, eu 1] at hT
  set N := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ))
  set Kg := blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0
  obtain ⟨hA0, -⟩ := blkAt_selfEnergy_mul (W := W) b (tauTwo b E X 0) (tauTwo b E X 1) N
  obtain ⟨hB0, -⟩ := blkAt_selfEnergy_mul (W := W) b (uTwo b E X 0) (uTwo b E X 1)
    (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ)
  have hGs : blkAt (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ) 0 0 = Kgᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose, ← mul_matrixExpect' _ _ hG]
  have hP0 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo *
      (kHat b E X * gRes b E X ω)ᴴ))) 0 0 = 0 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo *
        (kHat b E X * gRes b E X ω)ᴴ))) 0 0) = fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) :=
      funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hkd : ∀ Y : LayerMat W, blkAt (kHat b E X * (dressed b E X)⁻¹ * Y) 0 0 =
      kmOf b E X * blkAt Y 0 0 := fun Y => by
    rw [Matrix.mul_assoc, (blkAt_kHat_mul_zero b E X _).1, bl0, ← Matrix.mul_assoc, kmOf,
      (blkAt_kHat_mul_zero b E X _).1]; rfl
  have hthS : thetaOf b E X = ((1 - 2 * b : ℝ) : ℂ) * tauTwo b E X 0 + (b : ℂ) * tauTwo b E X 1 :=
    rfl
  have hrS : rhoOf b E X = ((1 - 2 * b : ℝ) : ℂ) * uTwo b E X 0 + (b : ℂ) * uTwo b E X 1 := rfl
  have h0 := (norm_blkAt_le _ 0 0).trans hT
  rw [blkAt_sub, hkd, blkAt_add, hP0, zero_add, blkAt_add, hA0, hB0, hGs, ← hthS, ← hrS] at h0
  have e : blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω *
        (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
        ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
          rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ)) =
      (blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω *
        (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          kmOf b E X * (thetaOf b E X • blkAt N 0 0 + rhoOf b E X • Kgᴴ)) +
        kmOf b E X * (thetaOf b E X • (blkAt N 0 0 - sOne b E X • (mOf b E X * (kmOf b E X)ᴴ)) +
          rhoOf b E X • (Kgᴴ - (kmOf b E X)ᴴ)) := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, smul_sub, smul_smul,
      Matrix.mul_assoc]
    abel
  rw [e]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ Cw / (W : ℝ) ^ 2 + CK * (Ct * (CN / (W : ℝ) ^ 2) + Cr * (CN / (W : ℝ) ^ 2)) := by
        refine add_le_add h0 ?_
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ((norm_blkAt_le _ _ _).trans hKD) ?_
          (norm_nonneg _) hCK)
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_smul_le _ _).trans (mul_le_mul hth hN0 (norm_nonneg _) hCt)
        · refine (norm_smul_le _ _).trans (mul_le_mul hrho ?_ (norm_nonneg _) hCr)
          rw [norm_conjTranspose_sub]; exact hKg
    _ = _ := by ring

end BlockBand.Transmission.SourceMixingBulk
