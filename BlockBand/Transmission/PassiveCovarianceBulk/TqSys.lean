module

public import BlockBand.Transmission.PassiveCovarianceBulk.AlpBlocks
public import BlockBand.Transmission.PassiveCovariance.TqSys

/-!
# Bulk-uniform `t^q` system

The blocks of `E[𝒢P_q𝒢ᴴ]` and the trace system for `t^q`, with constants and `W₀` uniform in
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

/-- **Blocks of `E[𝒢P_q𝒢ᴴ]`.**
Bulk-uniform copy of `tP_blocks` (constants uniform on `bulkInterval κ`). -/
theorem tP_blocks_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ q : Fin 2,
        (∀ r, ‖tP b E X q r‖ ≤ C) ∧ ‖yP b E X q‖ ≤ C ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) 0 0 -
          yP b E X q • (SourceMixing.mOf b E X * (SourceMixing.mOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) 1 1 -
          (SourceMixing.vOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) *
            conj (SourceMixing.vOf b E X)) • 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock_bulk hA hb0 hb hκ 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  set K := Cw + 1 + (Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD)
  have hK1 : Cw + 1 ≤ K := by
    have : 0 ≤ Cu + CD * (Cw + 1) * CD + CD * (1 + b * Cw) * CD := by positivity
    linarith
  refine ⟨K, max (max Wu WD) Ww, by positivity, fun W hW E hEκ X hX q => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw E hEκ X hX.posSemidef 2 le_rfl ![0, 2] (dP3 q) (norm_dP3_le q)
  have hGs : ∀ α β, Integrable (fun ω => (gRes b E X ω)ᴴ α β) μ := fun α β => by
    have h := (hw W hWw E hEκ X hX.posSemidef 1 (by norm_num) ![2] ![1, 1]
      SourceMixing.norm_ins1_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2] ![1, 1] α β) =
        fun ω => (gRes b E X ω)ᴴ α β := funext fun ω => by rw [wordVal_Gs1]
    rw [e] at h; exact h
  have ht : ∀ r, ‖tP b E X q r‖ ≤ Cw := fun r => by
    have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dP3 q)) r) =
        fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) r :=
      funext fun ω => by rw [wordVal_GPpGs]
    rw [e] at h; exact h
  have hx : ‖yP b E X q‖ ≤ Cw + 1 :=
    (norm_add_le _ _).trans (by
      have := norm_sig1_le hb0 hb (ht 0) (ht 1)
      have := norm_ind_le 0 q
      linarith)
  have hent : ∀ α β, Integrable
      (fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β) μ := fun α β => by
    have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dP3 q) α β) =
        fun ω => (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPpGs]
    rw [e] at h; exact h
  refine ⟨fun r => (ht r).trans (by linarith), hx.trans hK1, hent, ?_⟩
  have hT := hU W hWu E hEκ X hX 1 le_rfl ![2] (dP q) (norm_dP_le q)
  rw [Fin.sum_univ_one, Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2] (dP q)) =
      fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordVal_PpGs]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2] (dP q)) =
      fun ω => bProj q * (gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_PpGs]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 1 ![2] (dP q) 0) =
      fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_PpGs]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 ![2] (dP q) 0) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_PpGs]
  have e5 : matrixExpect μ (fun ω => bProj q * (gRes b E X ω)ᴴ) =
      bProj q * (matrixExpect μ (gRes b E X))ᴴ := by
    rw [← SourceMixing.mul_matrixExpect' _ _ hGs, SourceMixing.matrixExpect_conjTranspose]
  have e6 : matrixExpect μ (fun ω => (gRes b E X ω)ᴴ) = (matrixExpect μ (gRes b E X))ᴴ :=
    SourceMixing.matrixExpect_conjTranspose _
  rw [e1, e2, e3, e4, e5, e6, blkAt_bProj_mul, blkAt_bProj_mul, blkAt_conjTranspose,
    blkAt_conjTranspose] at hT
  obtain ⟨hT0, hT1⟩ := hT
  change ‖_ - SourceMixing.mOf b E X * ((ind 0 q) • _ + sig1 b (tP b E X q 0) (tP b E X q 1) • _)‖
    ≤ _ at hT0
  change ‖_ - SourceMixing.vOf b E X • ((ind 1 q) • _ + ((b : ℂ) * tP b E X q 0) • _)‖ ≤ _ at hT1
  rw [← add_smul] at hT0 hT1
  set T := matrixExpect μ (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  constructor
  · have e : blkAt T 0 0 - yP b E X q • (M * Mᴴ) =
        (blkAt T 0 0 - M * (yP b E X q • G0ᴴ)) + M * (yP b E X q • (G0ᴴ - Mᴴ)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((Cw + 1) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT0 ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hx ?_ (norm_nonneg _) (by positivity))
          rw [SourceMixing.norm_conjTranspose_sub]; exact hE0
      _ = (Cu + CD * (Cw + 1) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          simp only [K]; linarith
  · set y := ind 1 q + (b : ℂ) * tP b E X q 0
    have hy : ‖y‖ ≤ 1 + b * Cw := (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 q) (by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      exact mul_le_mul_of_nonneg_left (ht 0) hb0.le))
    have e : blkAt T 1 1 - (v * y * conj v) • 1 =
        (blkAt T 1 1 - v • (y • G1ᴴ)) + v • (y • (G1ᴴ - (v • 1)ᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_one, smul_sub, smul_sub, smul_smul, smul_smul]
      simp only [Complex.star_def, smul_smul, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hT1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hy ?_ (norm_nonneg _) (by positivity))
          rw [SourceMixing.norm_conjTranspose_sub]; exact hE1
      _ = (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hW2
          have : 0 ≤ CD * (Cw + 1) * CD := by positivity
          simp only [K]; linarith

/-- **The trace system for `t^q`.**
Bulk-uniform copy of `tP_system` (constants uniform on `bulkInterval κ`). -/
theorem tP_system_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ q : Fin 2,
        ‖yP b E X q‖ ≤ C ∧
        ‖tP b E X q 0 - yP b E X q * SourceMixing.aOf b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖tP b E X q 1 - SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖yP b E X q * (1 - SourceMixing.khOf b E X * SourceMixing.aOf b E X) -
          (ind 0 q + (b : ℂ) * SourceMixing.hOf b E X * ind 1 q)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := tP_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW E hEκ X hX q => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  obtain ⟨-, hx, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) E hEκ X hX q
  have ht : ∀ r, tP b E X q r = SourceMixing.blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ))) r := fun r =>
    SourceMixing.integral_blkTr _ hent r
  have d1 : ‖tP b E X q 0 - yP b E X q * SourceMixing.aOf b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tP b E X q 1 - SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (SourceMixing.norm_blkTr_sub_le _ 1 _).trans hb11
    rw [SourceMixing.normTrace_smul_one hW1, ← ht] at h
    have e : SourceMixing.vOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) *
        conj (SourceMixing.vOf b E X) =
        SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0) := by
      unfold SourceMixing.hOf; ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hup : C₁ / (W : ℝ) ^ 2 ≤ (K + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ (by linarith)) hW2'.le
  refine ⟨hx.trans (le_mul_of_one_le_left hC₁ (by linarith)), d1.trans hup, d2.trans hup, ?_⟩
  have hh : ‖SourceMixing.hOf b E X‖ ≤ CD * CD := by
    unfold SourceMixing.hOf
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  set h := SourceMixing.hOf b E X
  set A := SourceMixing.aOf b E X
  have e : yP b E X q * (1 - SourceMixing.khOf b E X * A) - (ind 0 q + (b : ℂ) * h * ind 1 q) =
      ((1 - 2 * b : ℝ) : ℂ) * (tP b E X q 0 - yP b E X q * A) +
        (b : ℂ) * (tP b E X q 1 - h * (ind 1 q + (b : ℂ) * tP b E X q 0)) +
        (b : ℂ) ^ 2 * h * (tP b E X q 0 - yP b E X q * A) := by
    unfold SourceMixing.khOf
    rw [show yP b E X q = ind 0 q + (((1 - 2 * b : ℝ) : ℂ) * tP b E X q 0 +
      (b : ℂ) * tP b E X q 1) from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tP b E X q 0 - yP b E X q * A)‖ +
        ‖(b : ℂ) * (tP b E X q 1 - h * (ind 1 q + (b : ℂ) * tP b E X q 0))‖ +
        ‖(b : ℂ) ^ 2 * h * (tP b E X q 0 - yP b E X q * A)‖ := norm_add₃_le
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
