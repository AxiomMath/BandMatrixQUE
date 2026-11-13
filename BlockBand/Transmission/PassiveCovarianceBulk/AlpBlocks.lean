module

public import BlockBand.Transmission.PassiveCovarianceBulk.MatchedScalars
public import BlockBand.Transmission.PassiveCovarianceBulk.SdQExpand
public import BlockBand.Transmission.PassiveCovariance.AlpBlocks
public import BlockBand.Transmission.PassiveCovariance.TauP
public import BlockBand.Transmission.PassiveCovariance.TqSys

/-!
# Bulk-uniform weighted/unweighted blocks and the `τ^p` system

The weighted and unweighted block expansions, the blocks of `E[𝒢P_p𝒢]` and the trace system
for `x_p`, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- **The weighted expansion, physical block.**
Bulk-uniform copy of `weightedBlock` (constants uniform on `bulkInterval κ`). -/
theorem weightedBlock_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₁, hC, hw⟩ := weightedExpansion_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  refine ⟨C, max (max W₁ WK) 1, hC, fun W hW E hEκ X hX ℓ hℓ wd D hD => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWK⟩, hW1⟩ := hW
  obtain ⟨hU, -, -, -⟩ := hK W hWK E hEκ X hX
  have h := (norm_blkAt_le _ 0 0).trans (hw W hW₁ E hEκ X hX ℓ hℓ wd D hD)
  rw [blkAt_sub, blkAt_kHatInv_mul hW1 hU, blkAt_add, blkAt_sum] at h
  simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).1] at h
  exact h

/-- **The unweighted expansion, both diagonal blocks.**
Bulk-uniform copy of `unweightedBlock` (constants uniform on `bulkInterval κ`). -/
theorem unweightedBlock_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₁, hC, hu⟩ := unweightedExpansion_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨CD, WD, hCD, hDB⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨C, max W₁ WD, hC, fun W hW E hEκ X hX ℓ hℓ wd D hD => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨-, -, -, -, bl0, bl1, -⟩ := hDB W hW.2 E hEκ X hX
  have h := hu W hW.1 E hEκ X hX ℓ hℓ wd D hD
  constructor
  · have h0 := (norm_blkAt_le _ 0 0).trans h
    rw [blkAt_sub, bl0, blkAt_add, blkAt_sum] at h0
    simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).1] at h0
    exact h0
  · have h1' := (norm_blkAt_le _ 1 1).trans h
    rw [blkAt_sub, bl1, blkAt_add, blkAt_sum] at h1'
    simp only [(SourceMixing.blkAt_selfEnergy_mul (W := W) b _ _ _).2] at h1'
    exact h1'

/-- **Blocks of `E[𝒢P_p𝒢]`.**
Bulk-uniform copy of `tauP_blocks` (constants uniform on `bulkInterval κ`). -/
theorem tauP_blocks_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖tauP b E X p r‖ ≤ C) ∧ ‖xP b E X p‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj p * gRes b E X ω) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) 0 0 -
          xP b E X p • (SourceMixing.mOf b E X * SourceMixing.mOf b E X)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) 1 1 -
          (SourceMixing.vOf b E X * (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.vOf b E X) •
            1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock_bulk hA hb0 hb hκ 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  set K := Cw + 1 + (Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD)
  have hK1 : Cw + 1 ≤ K := by
    have : 0 ≤ Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD := by positivity
    linarith
  refine ⟨K, max (max Wu WD) Ww, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, -, -, hE0, hE1, hG, -, -⟩ := hD W hWD E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 2 le_rfl ![0, 0] (dP3 p) (norm_dP3_le p)
  have ht : ∀ r, ‖tauP b E X p r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0] (dP3 p)) r) =
        fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj p * gRes b E X ω)) r :=
      funext fun ω => by rw [wordVal_GPpG]
    rw [e] at h; exact h
  have hx : ‖xP b E X p‖ ≤ Cw + 1 :=
    (norm_add_le _ _).trans (by
      have := norm_sig1_le hb0 hb (ht 0) (ht 1)
      have := norm_ind_le 0 p
      linarith)
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj p * gRes b E X ω) : LayerMat W) α β)
      μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0] (dP3 p) α β) =
        fun ω => (gRes b E X ω * (bProj p * gRes b E X ω) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPpG]
    rw [e] at h; exact h
  refine ⟨fun r => (ht r).trans (by linarith), hx.trans hK1, hent, ?_⟩
  have hT := hU W hWu E hEκ X hX 1 le_rfl ![0] (dP p) (norm_dP_le p)
  rw [Fin.sum_univ_one, Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordVal_PpG]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) =
      fun ω => bProj p * gRes b E X ω := funext fun ω => by rw [wordVal_PpG]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordAlpha_PpG]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_PpG]
  have e5 : matrixExpect μ (fun ω => bProj p * gRes b E X ω) =
      bProj p * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  rw [e1, e2, e3, e4, e5, blkAt_bProj_mul, blkAt_bProj_mul] at hT
  obtain ⟨hT0, hT1⟩ := hT
  change ‖_ - SourceMixing.mOf b E X * ((ind 0 p) • _ + sig1 b (tauP b E X p 0) (tauP b E X p 1) • _)‖
    ≤ _ at hT0
  change ‖_ - SourceMixing.vOf b E X • ((ind 1 p) • _ + ((b : ℂ) * tauP b E X p 0) • _)‖ ≤ _ at hT1
  rw [← add_smul] at hT0 hT1
  set T := matrixExpect μ (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  constructor
  · have e : blkAt T 0 0 - xP b E X p • (M * M) =
        (blkAt T 0 0 - M * (xP b E X p • G0)) + M * (xP b E X p • (G0 - M)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((Cw + 1) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT0 ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          exact (norm_smul_le _ _).trans (mul_le_mul hx hE0 (norm_nonneg _) (by positivity))
      _ = (Cu + CD * (Cw + 1) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          simp only [K]; linarith
  · set y := ind 1 p + (b : ℂ) * tauP b E X p 0
    have hy : ‖y‖ ≤ 1 + b * Cw := (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 p) (by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      exact mul_le_mul_of_nonneg_left (ht 0) hb0.le))
    have e : blkAt T 1 1 - (v * y * v) • 1 =
        (blkAt T 1 1 - v • (y • G1)) + v • (y • (G1 - v • 1)) := by
      simp only [smul_sub, smul_smul, mul_assoc]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          exact (norm_smul_le _ _).trans (mul_le_mul hy hE1 (norm_nonneg _) (by positivity))
      _ = (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (Cw + 1) * CD := by positivity
          simp only [K]; linarith

/-- **The trace system for `x_p`**: `x_p(1 - k_v⟨M²⟩) = [p=0] + bv²[p=1] + O(W⁻²)`.
Bulk-uniform copy of `tauP_system` (constants uniform on `bulkInterval κ`). -/
theorem tauP_system_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖xP b E X p‖ ≤ C ∧
        ‖xP b E X p * (1 - SourceMixing.kvOf b E X * SourceMixing.m2Of b E X) -
          (ind 0 p + (b : ℂ) * SourceMixing.vOf b E X ^ 2 * ind 1 p)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := tauP_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  obtain ⟨-, hx, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) E hEκ X hX p
  have ht : ∀ r, tauP b E X p r = SourceMixing.blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) r := fun r =>
    SourceMixing.integral_blkTr _ hent r
  have d1 : ‖tauP b E X p 0 - xP b E X p * SourceMixing.m2Of b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tauP b E X p 1 - SourceMixing.vOf b E X ^ 2 * (ind 1 p + (b : ℂ) * tauP b E X p 0)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 1 _).trans hb11
    rw [SourceMixing.normTrace_smul_one hW1, ← ht] at h
    have e : SourceMixing.vOf b E X * (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.vOf b E X =
        SourceMixing.vOf b E X ^ 2 * (ind 1 p + (b : ℂ) * tauP b E X p 0) := by ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  refine ⟨hx.trans (le_mul_of_one_le_left hC₁ (by linarith)), ?_⟩
  have hh : ‖SourceMixing.vOf b E X‖ ^ 2 ≤ CD * CD := by
    rw [sq]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  set v := SourceMixing.vOf b E X
  set m := SourceMixing.m2Of b E X
  have e : xP b E X p * (1 - SourceMixing.kvOf b E X * m) - (ind 0 p + (b : ℂ) * v ^ 2 * ind 1 p) =
      ((1 - 2 * b : ℝ) : ℂ) * (tauP b E X p 0 - xP b E X p * m) +
        (b : ℂ) * (tauP b E X p 1 - v ^ 2 * (ind 1 p + (b : ℂ) * tauP b E X p 0)) +
        (b : ℂ) ^ 2 * v ^ 2 * (tauP b E X p 0 - xP b E X p * m) := by
    unfold SourceMixing.kvOf
    rw [show xP b E X p = ind 0 p + (((1 - 2 * b : ℝ) : ℂ) * tauP b E X p 0 +
      (b : ℂ) * tauP b E X p 1) from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tauP b E X p 0 - xP b E X p * m)‖ +
        ‖(b : ℂ) * (tauP b E X p 1 - v ^ 2 * (ind 1 p + (b : ℂ) * tauP b E X p 0))‖ +
        ‖(b : ℂ) ^ 2 * v ^ 2 * (tauP b E X p 0 - xP b E X p * m)‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        simp only [norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.CovarianceBulk
