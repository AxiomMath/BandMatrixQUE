module

public import BlockBand.Transmission.SourceMixingBulk.ScalarTheta
public import BlockBand.Transmission.SourceMixing.ScalarRho
public import BlockBand.Transmission.SourceMixing.ScalarRhoEq
public import BlockBand.Transmission.LengthUniform.BulkWeighted

/-!
# The scalar system for `ρ₁`, uniformly on the bulk

The estimates `scalarRho_blocks` and `scalarRho` with constants uniform in `E ∈ bulkInterval κ`.
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

/-- The blocks of `E[𝒢P₂𝒢P₂𝒢ᴴ]`.
The version of `scalarRho_blocks` with constants uniform on `bulkInterval κ`. -/
theorem scalarRho_blocks_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        (∀ r, ‖uTwo b E X r‖ ≤ C) ∧ ‖rhoOf b E X‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω *
          (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))))) 0 0 -
          ((thetaOf b E X * sOne b E X) • (mOf b E X * (mOf b E X * (mOf b E X)ᴴ)) +
            rhoOf b E X • (mOf b E X * (mOf b E X)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))))) 1 1 -
          (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
            vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X)) • 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion_bulk hA hb0 hb hκ 2 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  obtain ⟨C1, W1, hC1, hS1⟩ := scalarS1_blocks_bulk hA hb0 hb hκ
  obtain ⟨C1', W1', hC1', hS1'⟩ := scalarS1_bulk hA hb0 hb hκ
  obtain ⟨Ct, Wt, hCt, hTh⟩ := scalarTheta_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  set Cr := (1 - 2 * b) * Cw + b * Cw
  have hCr : 0 ≤ Cr := by have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  set K0 := Cu + CD * (Ct * C1 + Cr * CD)
  set K1 := Cu + CD * ((1 + b * Ct) * (C1 + C1') + b * Cw * CD)
  refine ⟨Cw + Cr + K0 + K1, max (max (max Wu WD) (max Ww W1)) (max (max W1' Wt) Wf),
    by positivity, fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWu, hWD⟩, hWw, hW1⟩, ⟨hW1', hWt⟩, hWf⟩ := hW
  obtain ⟨hW1r, -, hM, hv, bl0, bl1, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨hT00, hT11⟩ := hS1 W hW1 E hEκ X hX
  obtain ⟨-, ht2, -⟩ := hS1' W hW1' E hEκ X hX
  obtain ⟨htau, hth, -, -, -⟩ := hTh W hWt E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 3 le_rfl ![0, 0, 2] ![1, SourceMixing.pTwo, SourceMixing.pTwo, 1] norm_ins4_le
  have hu : ∀ r, ‖uTwo b E X r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2]
        ![1, SourceMixing.pTwo, SourceMixing.pTwo, 1]) r) = fun ω => blkTr (gRes b E X ω *
          (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))) r :=
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
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω *
      (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) : LayerMat W) α β) μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2] ![1, SourceMixing.pTwo, SourceMixing.pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GPGPGs]
    rw [e] at h; exact h
  have hK0 : 0 ≤ K0 := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  refine ⟨fun r => (hu r).trans (by linarith), hrho.trans (by linarith), hent, ?_⟩
  have hT := hU W hWu E hEκ X hX 2 le_rfl wdR dR norm_dR_le
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdR dR) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_R]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdR dR) =
      fun ω => SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) := funext fun ω => by rw [wordVal_R]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR dR 0) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r :=
    fun r => funext fun ω => by rw [wordAlpha_R0]
  have e4 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 2 wdR dR 1) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))) r :=
    fun r => funext fun ω => by rw [wordAlpha_R1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR dR 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_R0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 wdR dR 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_R1]
  rw [e1, e2, e3 0, e3 1, e4 0, e4 1, e5, e6] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * gRes b E X ω)) r ∂μ) = tauTwo b E X r :=
    fun r => rfl
  have eu : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω *
      (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))) r ∂μ) = uTwo b E X r := fun r => rfl
  rw [et 0, et 1, eu 0, eu 1] at hT
  set U := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω *
    (SourceMixing.pTwo * (gRes b E X ω)ᴴ))))
  set T := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  obtain ⟨hA0, hA1⟩ := blkAt_selfEnergy_mul (W := W) b (tauTwo b E X 0) (tauTwo b E X 1) T
  obtain ⟨hB0, hB1⟩ := blkAt_selfEnergy_mul (W := W) b (uTwo b E X 0) (uTwo b E X 1)
    (matrixExpect μ fun ω => (gRes b E X ω)ᴴ)
  have hGs0 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 0 0 = G0ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hGs1 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hP0 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))
      0 0 = 0 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hP1 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)))
      1 1 = blkAt T 1 1 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) 1 1) =
        fun ω => blkAt (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) 1 1 :=
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

/-- The scalar equation for `ρ₁`, together with the trace equation for `u₁`.
The version of `scalarRho` with constants uniform on `bulkInterval κ`. -/
theorem scalarRho_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X + rhoOf b E X * aOf b E X)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖rhoOf b E X * (1 - khOf b E X * aOf b E X) -
          (khOf b E X * (thetaOf b E X * sOne b E X * bOf b E X) +
            (b : ℂ) * vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := scalarRho_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  obtain ⟨-, -, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) E hEκ X hX
  have hu : ∀ r, uTwo b E X r = blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))))) r :=
    fun r => integral_blkTr _ hent r
  have d1 : ‖uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X + rhoOf b E X * aOf b E X)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_add, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, mul_add, mul_left_comm,
      mul_left_comm (W : ℂ)⁻¹ (rhoOf b E X), ← hu] at h
    exact h
  have d2 : ‖uTwo b E X 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
      vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X))‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 1 _).trans hb11
    rw [normTrace_smul_one hW1, ← hu] at h
    exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hup : C₁ / (W : ℝ) ^ 2 ≤ (K + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ (by linarith)) hW2'.le
  refine ⟨d1.trans hup, ?_⟩
  have hh : ‖hOf b E X‖ ≤ CD * CD := by
    unfold hOf; rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have e : rhoOf b E X * (1 - khOf b E X * aOf b E X) -
      (khOf b E X * (thetaOf b E X * sOne b E X * bOf b E X) +
        (b : ℂ) * vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1) =
      ((1 - 2 * b : ℝ) : ℂ) * (uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X +
          rhoOf b E X * aOf b E X)) +
        (b : ℂ) * (uTwo b E X 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
          vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X))) +
        (b : ℂ) ^ 2 * hOf b E X * (uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X +
          rhoOf b E X * aOf b E X)) := by
    unfold khOf hOf
    rw [show rhoOf b E X = ((1 - 2 * b : ℝ) : ℂ) * uTwo b E X 0 + (b : ℂ) * uTwo b E X 1 from rfl]
    ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  refine (norm_add₃_le).trans ?_
  calc _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.SourceMixingBulk
