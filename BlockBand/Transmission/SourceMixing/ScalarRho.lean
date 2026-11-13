module

public import BlockBand.Transmission.SourceMixing.ScalarTheta

/-!
# The scalar system for `ρ₁` (word `w = P₂𝒢P₂𝒢ᴴ`)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E`
only, uniformly in `W ≥ W₀` and `X`.

The blocks of the three-resolvent mean `E[𝒢P₂𝒢P₂𝒢ᴴ]` up to `O(W⁻²)`.

`U = E[𝒢P₂𝒢P₂𝒢ᴴ]`, `u_r = ⟨U⟩_r` (`uTwo`), `ρ₁ = cu₁ + bu₂` (`rhoOf`), `B = ⟨M²Mᴴ⟩` (`bOf`).
* `scalarRho_blocks`: `|u_r|, |ρ₁| ≤ C`; `‖U₀₀ - (θs₁M²Mᴴ + ρ₁MMᴴ)‖ ≤ C/W²`;
  `‖U₁₁ - (v(1 + bτ₁)t₂ + bu₁h)·I‖ ≤ C/W²`;
* `scalarRho` (proved in the sibling module): `|ρ₁(1 - k_hA) - (k_hθs₁B + bv(1 + bτ₁)t₂)| ≤ C/W²`.
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

/-- `u_r = E⟨(𝒢P₂𝒢P₂𝒢ᴴ)_{rr}⟩`. -/
def uTwo (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (r : Fin 2) : ℂ :=
  ∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))) r
    ∂layerLaw W b .oneBlockOnePort

/-- `ρ₁ = cu₁ + bu₂`. -/
def rhoOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ((1 - 2 * b : ℝ) : ℂ) * uTwo b E X 0 + (b : ℂ) * uTwo b E X 1

/-- `B = ⟨M²Mᴴ⟩`. -/
def bOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (mOf b E X * (mOf b E X * (mOf b E X)ᴴ)).trace

/-- Letters of `P₂𝒢P₂𝒢ᴴ` (and of `P₂𝒢P₂(K̂𝒢)ᴴ` with the second letter `3`). -/
def wdR : Fin 2 → Fin 4 := ![0, 2]

/-- Insertions `P₂, P₂, 1`. -/
def dR : Fin 3 → LayerMat W := ![pTwo, pTwo, 1]

theorem norm_dR_le (j : Fin 3) : ‖(dR j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_portProj_le
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem wordVal_R (Kh G : LayerMat W) : wordVal Kh G wdR dR = pTwo * (G * (pTwo * Gᴴ)) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wdR, dR, wLetter, Matrix.mul_assoc]

theorem wordAlpha_R0 (Kh G : LayerMat W) : wordAlpha Kh G 2 wdR dR 0 = pTwo * G := by
  simp [wordAlpha, wdR, dR, wLeft]

theorem wordAlpha_R1 (Kh G : LayerMat W) :
    wordAlpha Kh G 2 wdR dR 1 = pTwo * (G * (pTwo * Gᴴ)) := by
  simp [wordAlpha, wdR, dR, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_R0 (Kh G : LayerMat W) : wordGamma Kh G 2 wdR dR 0 = G * (pTwo * Gᴴ) := by
  simp [wordGamma, wdR, dR, wRight, wordVal, wLetter]

theorem wordGamma_R1 (Kh G : LayerMat W) : wordGamma Kh G 2 wdR dR 1 = Gᴴ := by
  simp [wordGamma, wdR, dR, wRight, wordVal]

theorem wordVal_GPGPGs (Kh G : LayerMat W) :
    wordVal Kh G ![0, 0, 2] ![1, pTwo, pTwo, 1] = G * (pTwo * (G * (pTwo * Gᴴ))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wLetter, Matrix.mul_assoc]

theorem norm_ins4_le (j : Fin 4) : ‖(![1, pTwo, pTwo, 1] : Fin 4 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_portProj_le
  · exact norm_portProj_le
  · exact norm_one_matrix_le

/-- The blocks of `E[𝒢P₂𝒢P₂𝒢ᴴ]`. -/
theorem scalarRho_blocks (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        (∀ r, ‖uTwo b E X r‖ ≤ C) ∧ ‖rhoOf b E X‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (pTwo * (gRes b E X ω *
          (pTwo * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))))) 0 0 -
          ((thetaOf b E X * sOne b E X) • (mOf b E X * (mOf b E X * (mOf b E X)ᴴ)) +
            rhoOf b E X • (mOf b E X * (mOf b E X)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))))) 1 1 -
          (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
            vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X)) • 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion hA hb0 hb h1 h2 2 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound hA hb0 hb h1 h2 3 1
  obtain ⟨C1, W1, hC1, hS1⟩ := scalarS1_blocks hA hb0 hb h1 h2
  obtain ⟨C1', W1', hC1', hS1'⟩ := scalarS1 hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTh⟩ := scalarTheta_blocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  set Cr := (1 - 2 * b) * Cw + b * Cw
  have hCr : 0 ≤ Cr := by have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  set K0 := Cu + CD * (Ct * C1 + Cr * CD)
  set K1 := Cu + CD * ((1 + b * Ct) * (C1 + C1') + b * Cw * CD)
  refine ⟨Cw + Cr + K0 + K1, max (max (max Wu WD) (max Ww W1)) (max (max W1' Wt) Wf),
    by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWu, hWD⟩, hWw, hW1⟩, ⟨hW1', hWt⟩, hWf⟩ := hW
  obtain ⟨hW1r, -, hM, hv, bl0, bl1, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  obtain ⟨hT00, hT11⟩ := hS1 W hW1 X hX
  obtain ⟨-, ht2, -⟩ := hS1' W hW1' X hX
  obtain ⟨htau, hth, -, -, -⟩ := hTh W hWt X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw X hX.posSemidef 3 le_rfl ![0, 0, 2] ![1, pTwo, pTwo, 1] norm_ins4_le
  have hu : ∀ r, ‖uTwo b E X r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2]
        ![1, pTwo, pTwo, 1]) r) = fun ω => blkTr (gRes b E X ω *
          (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))) r :=
      funext fun ω => by rw [wordVal_GPGPGs]
    rw [e] at h; exact h
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hrho : ‖rhoOf b E X‖ ≤ Cr := by
    unfold rhoOf
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, nc, nb]
    have : 0 ≤ 1 - 2 * b := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (hu 0) this) (mul_le_mul_of_nonneg_left (hu 1) hb0.le)
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (pTwo * (gRes b E X ω *
      (pTwo * (gRes b E X ω)ᴴ))) : LayerMat W) α β) μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2] ![1, pTwo, pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GPGPGs]
    rw [e] at h; exact h
  have hK0 : 0 ≤ K0 := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  refine ⟨fun r => (hu r).trans (by linarith), hrho.trans (by linarith), hent, ?_⟩
  have hT := hU W hWu X hX 2 le_rfl wdR dR norm_dR_le
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdR dR) =
      fun ω => gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_R]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdR dR) =
      fun ω => pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) := funext fun ω => by rw [wordVal_R]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR dR 0) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * gRes b E X ω)) r :=
    fun r => funext fun ω => by rw [wordAlpha_R0]
  have e4 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR dR 1) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))) r :=
    fun r => funext fun ω => by rw [wordAlpha_R1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR dR 0) =
      fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_R0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR dR 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_R1]
  rw [e1, e2, e3 0, e3 1, e4 0, e4 1, e5, e6] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * gRes b E X ω)) r ∂μ) = tauTwo b E X r :=
    fun r => rfl
  have eu : ∀ r, (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω *
      (pTwo * (gRes b E X ω)ᴴ)))) r ∂μ) = uTwo b E X r := fun r => rfl
  rw [et 0, et 1, eu 0, eu 1] at hT
  set U := matrixExpect μ (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω *
    (pTwo * (gRes b E X ω)ᴴ))))
  set T := matrixExpect μ (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  obtain ⟨hA0, hA1⟩ := blkAt_selfEnergy_mul (W := W) b (tauTwo b E X 0) (tauTwo b E X 1) T
  obtain ⟨hB0, hB1⟩ := blkAt_selfEnergy_mul (W := W) b (uTwo b E X 0) (uTwo b E X 1)
    (matrixExpect μ fun ω => (gRes b E X ω)ᴴ)
  have hGs0 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 0 0 = G0ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hGs1 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hP0 : blkAt (matrixExpect μ fun ω => pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))
      0 0 = 0 := by
    have e : (fun ω => blkAt (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hP1 : blkAt (matrixExpect μ fun ω => pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)))
      1 1 = blkAt T 1 1 := by
    have e : (fun ω => blkAt (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))) 1 1) =
        fun ω => blkAt (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) 1 1 :=
      funext fun ω => blkAt_portProj_mul_one _
    rw [blkAt_matrixExpect, e]; rfl
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  have hthS : thetaOf b E X = ((1 - 2 * b : ℝ) : ℂ) * tauTwo b E X 0 + (b : ℂ) * tauTwo b E X 1 :=
    rfl
  have hrS : rhoOf b E X = ((1 - 2 * b : ℝ) : ℂ) * uTwo b E X 0 + (b : ℂ) * uTwo b E X 1 := rfl
  constructor
  · have h0 := (norm_blkAt_le _ 0 0).trans hT
    rw [blkAt_sub, bl0, blkAt_add, hP0, zero_add, blkAt_add, hA0, hB0, hGs0, ← hthS, ← hrS] at h0
    have e : blkAt U 0 0 - ((thetaOf b E X * sOne b E X) • (mOf b E X * (mOf b E X *
          (mOf b E X)ᴴ)) + rhoOf b E X • (mOf b E X * (mOf b E X)ᴴ)) =
        (blkAt U 0 0 - mOf b E X * (thetaOf b E X • blkAt T 0 0 + rhoOf b E X • G0ᴴ)) +
          mOf b E X * (thetaOf b E X • (blkAt T 0 0 - sOne b E X • (mOf b E X * (mOf b E X)ᴴ)) +
            rhoOf b E X • (G0ᴴ - (mOf b E X)ᴴ)) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, smul_sub, smul_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * (Ct * (C1 / (W : ℝ) ^ 2) + Cr * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add h0 ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_smul_le _ _).trans (mul_le_mul hth hT00 (norm_nonneg _) hCt)
          · refine (norm_smul_le _ _).trans (mul_le_mul hrho ?_ (norm_nonneg _) hCr)
            rw [norm_conjTranspose_sub]; exact hE0
      _ = K0 / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hW2
  · have h1' := (norm_blkAt_le _ 1 1).trans hT
    rw [blkAt_sub, bl1, blkAt_add, hP1, blkAt_add, hA1, hB1, hGs1] at h1'
    -- `T₁₁ ≈ t₂·I`
    have hT1 : ‖blkAt T 1 1 - tTwo b E X 1 • 1‖ ≤ (C1 + C1') / (W : ℝ) ^ 2 := by
      have e : blkAt T 1 1 - tTwo b E X 1 • 1 =
          (blkAt T 1 1 - (vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X)) • 1) +
            (hOf b E X * (1 + (b : ℂ) * tTwo b E X 0) - tTwo b E X 1) • 1 := by
        rw [show hOf b E X * (1 + (b : ℂ) * tTwo b E X 0) =
          vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X) by unfold hOf; ring,
          sub_smul]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [add_div]
      refine add_le_add hT11 ((norm_smul_one_le _).trans ?_)
      rw [norm_sub_rev]; exact ht2
    have hτ : ‖1 + (b : ℂ) * tauTwo b E X 0‖ ≤ 1 + b * Ct := by
      calc ‖1 + (b : ℂ) * tauTwo b E X 0‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * tauTwo b E X 0‖ :=
            norm_add_le _ _
        _ ≤ 1 + b * Ct := by
            rw [norm_one, norm_mul, nb]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (htau 0) hb0.le)
    have hbu : ‖(b : ℂ) * uTwo b E X 0‖ ≤ b * Cw := by
      rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hu 0) hb0.le
    have e : blkAt U 1 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
          vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X)) • 1 =
        (blkAt U 1 1 - vOf b E X • (blkAt T 1 1 + (((b : ℂ) * tauTwo b E X 0) • blkAt T 1 1 +
          ((b : ℂ) * uTwo b E X 0) • G1ᴴ))) +
        vOf b E X • ((1 + (b : ℂ) * tauTwo b E X 0) • (blkAt T 1 1 - tTwo b E X 1 • 1) +
          ((b : ℂ) * uTwo b E X 0) • (G1ᴴ - (vOf b E X • 1)ᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_one]
      simp only [smul_sub, smul_add, add_smul, one_smul, smul_smul, Complex.star_def, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Ct) * ((C1 + C1') / (W : ℝ) ^ 2) +
          b * Cw * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add h1' ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_smul_le _ _).trans (mul_le_mul hτ hT1 (norm_nonneg _) (by positivity))
          · refine (norm_smul_le _ _).trans (mul_le_mul hbu ?_ (norm_nonneg _) (by positivity))
            rw [norm_conjTranspose_sub]; exact hE1
      _ = K1 / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hW2

end BlockBand.Transmission.SourceMixing
