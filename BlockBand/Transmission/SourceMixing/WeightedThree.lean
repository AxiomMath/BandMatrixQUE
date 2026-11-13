module

public import BlockBand.Transmission.SourceMixing.ScalarRhoEq

/-!
# The three-resolvent weighted word: `E[L𝒢₂₂L*] = KM(θs₁M + ρ₁)(KM)ᴴ + O(W⁻²)`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic
strictly passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants
depend on `b, E` only, uniformly in `W ≥ W₀` and `X`.

* `mixedBlock`: `N = E[𝒢P₂(K̂𝒢)ᴴ]` has `‖N₀₀ - s₁M(KM)ᴴ‖ ≤ C/W²`;
* `threeBlock`: `‖blkAt(K̂E[𝒢P₂𝒢P₂(K̂𝒢)ᴴ]) 0 0 - ((θs₁)KM·M(KM)ᴴ + ρ₁KM(KM)ᴴ)‖ ≤ C/W²`;
* `blkAt_three`: pointwise, `blkAt(K̂𝒢P₂𝒢P₂(K̂𝒢)ᴴ) 0 0 = L𝒢₂₂L*`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem blkAt_mul_pTwo_mul (A Y : LayerMat W) (r s : Fin 2) :
    blkAt (A * (pTwo * Y)) r s = blkAt A r 1 * blkAt Y 1 s := by
  rw [← Matrix.mul_assoc, blkAt_mul, Fin.sum_univ_two, blkAt_mul A pTwo, blkAt_mul A pTwo,
    Fin.sum_univ_two, Fin.sum_univ_two, blkAt_portProj, blkAt_portProj, blkAt_portProj,
    blkAt_portProj]
  simp

/-- `blkAt(K̂𝒢P₂𝒢P₂(K̂𝒢)ᴴ) 0 0 = L𝒢₂₂L*` pointwise. -/
theorem blkAt_three (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    blkAt (kHat b E X * (gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo *
        (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 =
      lAt E (boundaryZ b E) X ω * g22 E (boundaryZ b E) X ω * (lAt E (boundaryZ b E) X ω)ᴴ := by
  set G := gRes b E X ω
  have h01 : blkAt (wLetter (kHat b E X) G 1) 0 1 = lAt E (boundaryZ b E) X ω := by
    rw [blkAt_wLetter]; rfl
  have h10 : blkAt (wLetter (kHat b E X) G 3) 1 0 = (lAt E (boundaryZ b E) X ω)ᴴ := by
    rw [blkAt_wLetter]; rfl
  have h11 : blkAt (wLetter (kHat b E X) G 0) 1 1 = g22 E (boundaryZ b E) X ω := by
    rw [blkAt_wLetter]; rfl
  rw [← Matrix.mul_assoc, blkAt_mul_pTwo_mul, blkAt_mul_pTwo_mul]
  change blkAt (wLetter (kHat b E X) G 1) 0 1 * (blkAt (wLetter (kHat b E X) G 0) 1 1 *
    blkAt (wLetter (kHat b E X) G 3) 1 0) = _
  rw [h01, h10, h11, Matrix.mul_assoc]

/-- Letters of `P₂𝒢P₂(K̂𝒢)ᴴ`. -/
def wdR3 : Fin 2 → Fin 4 := ![0, 3]

theorem wordVal_R3 (Kh G : LayerMat W) :
    wordVal Kh G wdR3 dR = pTwo * (G * (pTwo * (Kh * G)ᴴ)) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wdR3, dR, wLetter, Matrix.mul_assoc]

theorem wordAlpha_R30 (Kh G : LayerMat W) : wordAlpha Kh G 2 wdR3 dR 0 = pTwo * G := by
  simp [wordAlpha, wdR3, dR, wLeft]

theorem wordAlpha_R31 (Kh G : LayerMat W) :
    wordAlpha Kh G 2 wdR3 dR 1 = pTwo * (G * (pTwo * Gᴴ)) := by
  simp [wordAlpha, wdR3, dR, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_R30 (Kh G : LayerMat W) :
    wordGamma Kh G 2 wdR3 dR 0 = G * (pTwo * (Kh * G)ᴴ) := by
  simp [wordGamma, wdR3, dR, wRight, wordVal, wLetter]

theorem wordGamma_R31 (Kh G : LayerMat W) : wordGamma Kh G 2 wdR3 dR 1 = (Kh * G)ᴴ := by
  simp [wordGamma, wdR3, dR, wRight, wordVal]

/-- **The mixed two-resolvent block** `N₀₀ = s₁M(KM)ᴴ + O(W⁻²)`. -/
theorem mixedBlock (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 -
          sOne b E X • (mOf b E X * (kmOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 -
          kmOf b E X‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion hA hb0 hb h1 h2 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  refine ⟨Cu + CD * Cf * CK + CK, max (max Wu WD) (max WK Wf), by positivity,
    fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWK, hWf⟩ := hW
  obtain ⟨-, -, hM, -, bl0, -, -, -, hG, -, -⟩ := hD W hWD X hX
  obtain ⟨-, -, -, hKE⟩ := hK W hWK X hX
  obtain ⟨-, hs, -⟩ := hF W hWf X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  have hKg : ‖blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0 - kmOf b E X‖ ≤
      CK / (W : ℝ) ^ 2 := by
    rw [kmOf, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hKE
  refine ⟨?_, hKg.trans (div_le_div_of_nonneg_right (by
    have : 0 ≤ CD * Cf * CK := by positivity
    linarith) hW2)⟩
  have hT := hU W hWu X hX 1 le_rfl wdStar dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordVal_star]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => pTwo * (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_star]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r :=
    fun r => funext fun ω => by rw [wordAlpha_star]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_star]
  rw [e1, e2, e3 0, e3 1, e4] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r ∂μ) = tTwo b E X r :=
    fun r => rfl
  rw [et 0, et 1] at hT
  obtain ⟨hS0, -⟩ := blkAt_selfEnergy_mul (W := W) b (tTwo b E X 0) (tTwo b E X 1)
    (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ)
  have hGs : blkAt (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ) 0 0 =
      (blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0)ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose, mul_matrixExpect' _ _ hG]
  have hP0 : blkAt (matrixExpect μ fun ω => pTwo * (kHat b E X * gRes b E X ω)ᴴ) 0 0 = 0 := by
    have e : (fun ω => blkAt (pTwo * (kHat b E X * gRes b E X ω)ᴴ) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have h0 := (norm_blkAt_le _ 0 0).trans hT
  rw [blkAt_sub, bl0, blkAt_add, hP0, zero_add, hS0, hGs] at h0
  set Kg := blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0
  have e : blkAt (matrixExpect μ fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))
        0 0 - sOne b E X • (mOf b E X * (kmOf b E X)ᴴ) =
      (blkAt (matrixExpect μ fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ)) 0 0 -
        mOf b E X * (sOne b E X • Kgᴴ)) + mOf b E X * (sOne b E X • (Kgᴴ - (kmOf b E X)ᴴ)) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * (Cf * (CK / (W : ℝ) ^ 2)) := by
        refine add_le_add h0 ?_
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
        refine (norm_smul_le _ _).trans (mul_le_mul hs ?_ (norm_nonneg _) hCf)
        rw [norm_conjTranspose_sub]; exact hKg
    _ = (Cu + CD * Cf * CK) / (W : ℝ) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hW2

/-- **The three-resolvent weighted block.** -/
theorem threeBlock (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (pTwo * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
            rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cw, Ww, hCw, hW3⟩ := weightedExpansion hA hb0 hb h1 h2 2 1
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨CN, WN, hCN, hN⟩ := mixedBlock hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTh⟩ := scalarTheta_blocks hA hb0 hb h1 h2
  obtain ⟨Cr, Wr, hCr, hRh⟩ := scalarRho_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  refine ⟨Cw + CK * (Ct * CN + Cr * CN), max (max (max Ww WK) (max WN Wt)) (max Wr WD),
    by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWK⟩, hWN, hWt⟩, hWr, hWD⟩ := hW
  obtain ⟨-, -, hKD, -⟩ := hK W hWK X hX
  obtain ⟨hN0, hKg⟩ := hN W hWN X hX
  obtain ⟨-, hth, -, -, -⟩ := hTh W hWt X hX
  obtain ⟨-, hrho, -, -, -⟩ := hRh W hWr X hX
  obtain ⟨-, -, -, -, bl0, -, -, -, hG, -, -⟩ := hD W hWD X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hT := hW3 W hWw X hX 2 le_rfl wdR3 dR norm_dR_le
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdR3 dR) =
      fun ω => gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_R3]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdR3 dR) =
      fun ω => pTwo * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_R3]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR3 dR 0) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * gRes b E X ω)) r :=
    fun r => funext fun ω => by rw [wordAlpha_R30]
  have e4 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR3 dR 1) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))) r :=
    fun r => funext fun ω => by rw [wordAlpha_R31]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR3 dR 0) =
      fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_R30]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR3 dR 1) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_R31]
  rw [e1, e2, e3 0, e3 1, e4 0, e4 1, e5, e6] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * gRes b E X ω)) r ∂μ) = tauTwo b E X r :=
    fun r => rfl
  have eu : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω *
      (pTwo * (gRes b E X ω)ᴴ)))) r ∂μ) = uTwo b E X r := fun r => rfl
  rw [et 0, et 1, eu 0, eu 1] at hT
  set N := matrixExpect μ (fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))
  set Kg := blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0
  obtain ⟨hA0, -⟩ := blkAt_selfEnergy_mul (W := W) b (tauTwo b E X 0) (tauTwo b E X 1) N
  obtain ⟨hB0, -⟩ := blkAt_selfEnergy_mul (W := W) b (uTwo b E X 0) (uTwo b E X 1)
    (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ)
  have hGs : blkAt (matrixExpect μ fun ω => (kHat b E X * gRes b E X ω)ᴴ) 0 0 = Kgᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose, ← mul_matrixExpect' _ _ hG]
  have hP0 : blkAt (matrixExpect μ fun ω => pTwo * (gRes b E X ω * (pTwo *
      (kHat b E X * gRes b E X ω)ᴴ))) 0 0 = 0 := by
    have e : (fun ω => blkAt (pTwo * (gRes b E X ω * (pTwo *
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
        (pTwo * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
        ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
          rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ)) =
      (blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω *
        (pTwo * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
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

end BlockBand.Transmission.SourceMixing
