module

public import BlockBand.Transmission.SourceMixing.ScalarS1
public import BlockBand.Transmission.LengthUniform.BulkWeighted

/-!
# Bulk-uniform unweighted expansion and the scalar system for `s₁`

The unweighted expansion `E[𝒢w] = D⁻¹(E w + Σ_j 𝒮_j Eγ_j) + O(W⁻²)`, the blocks of
`E[𝒢P₂𝒢ᴴ]` and the scalar system for `s₁`, uniformly in `E ∈ bulkInterval κ`: the constants and `W₀`
depend only on `b` and the bulk margin `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The unweighted expansion** `E[𝒢w] = D⁻¹(E w + Σ_j 𝒮_j Eγ_j) + O(W⁻²)`. -/
theorem unweightedExpansion_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) -
          (dressed b E X)⁻¹ *
            (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) +
            ∑ j, selfEnergy b
                (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
                  ∂layerLaw W b .oneBlockOnePort)
                (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
                  ∂layerLaw W b .oneBlockOnePort) *
              matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Ce, We, hCe, hexp⟩ := meanExpansion_bulk hA hb0 hb hκ Lw Kd
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  refine ⟨CK * Ce, max We WK, by positivity, fun W hW E hE X hX ℓ hℓ wd D hD => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  obtain ⟨hU, hDn, -, -⟩ := hK W (le_trans (le_max_right _ _) hW) E hE X hX
  have he := hexp W (le_trans (le_max_left _ _) hW) E hE X hX ℓ hℓ wd D hD
  set T := matrixExpect (layerLaw W b .oneBlockOnePort)
    (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D)
  set R := matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) +
    ∑ j, selfEnergy b
        (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
          ∂layerLaw W b .oneBlockOnePort)
        (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
          ∂layerLaw W b .oneBlockOnePort) *
      matrixExpect (layerLaw W b .oneBlockOnePort)
        (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)
  have hDinvD : (dressed b E X)⁻¹ * dressed b E X = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have e : T - (dressed b E X)⁻¹ * R = (dressed b E X)⁻¹ * (dressed b E X * T - R) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hDinvD, Matrix.one_mul]
  have he' : ‖dressed b E X * T - R‖ ≤ Ce / (W : ℝ) ^ 2 := by
    have : dressed b E X * T - R = dressed b E X * T -
        matrixExpect (layerLaw W b .oneBlockOnePort)
          (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) -
        ∑ j, selfEnergy b
            (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
              ∂layerLaw W b .oneBlockOnePort)
            (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
              ∂layerLaw W b .oneBlockOnePort) *
          matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) := by
      simp only [R]; abel
    rw [this]; exact he
  rw [e]
  calc _ ≤ ‖(dressed b E X)⁻¹‖ * ‖dressed b E X * T - R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ CK * (Ce / (W : ℝ) ^ 2) := mul_le_mul hDn he' (norm_nonneg _) hCK
    _ = _ := by ring

/-- **Blocks of `E[𝒢P₂𝒢ᴴ]`.** -/
theorem scalarS1_blocks_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) 0 0 -
          sOne b E X • (mOf b E X * (mOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) 1 1 -
          (vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X)) • 1‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedExpansion_bulk hA hb0 hb hκ 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  refine ⟨Cu + CD * Cf * CD + CD * (1 + b * Cw) * CD, max (max Wu WD) (max Wf Ww), by positivity,
    fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWu, hWD⟩, hWf, hWw⟩ := hW
  obtain ⟨-, -, hM, hv, bl0, bl1, hE0, hE1, -, -, -⟩ := hD W hWD E hE X hX
  obtain ⟨-, hs, -⟩ := hF W hWf E hE X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hT := hU W hWu E hE X hX 1 le_rfl wdGs dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdGs dStar2) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordVal_Gs]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdGs dStar2) =
      fun ω => SourceMixing.pTwo * (gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_Gs]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdGs dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) r :=
    fun r => funext fun ω => by rw [wordAlpha_Gs]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdGs dStar2 0) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_Gs]
  rw [e1, e2, e3 0, e3 1, e4] at hT
  have et : ∀ r, (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) r ∂μ) = tTwo b E X r :=
    fun r => rfl
  rw [et 0, et 1] at hT
  set T := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  obtain ⟨hS0, hS1⟩ := blkAt_selfEnergy_mul (W := W) b (tTwo b E X 0) (tTwo b E X 1)
    (matrixExpect μ fun ω => (gRes b E X ω)ᴴ)
  have hGs0 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 0 0 = G0ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hGs1 : blkAt (matrixExpect μ fun ω => (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    rw [matrixExpect_conjTranspose, blkAt_conjTranspose]
  have hP0 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * (gRes b E X ω)ᴴ) 0 0 = 0 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (gRes b E X ω)ᴴ) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  have hP1 : blkAt (matrixExpect μ fun ω => SourceMixing.pTwo * (gRes b E X ω)ᴴ) 1 1 = G1ᴴ := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (gRes b E X ω)ᴴ) 1 1) =
        fun ω => blkAt ((gRes b E X ω)ᴴ) 1 1 := funext fun ω => blkAt_portProj_mul_one _
    rw [blkAt_matrixExpect, e, ← blkAt_matrixExpect, hGs1]
  have hst : ‖(b : ℂ) * tTwo b E X 0‖ ≤ b * Cw := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![0, 2] ![1, SourceMixing.pTwo, 1] norm_ins_le).2.2.2.2 0
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, SourceMixing.pTwo, 1]) 0) =
        fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) 0 :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h
    exact mul_le_mul_of_nonneg_left h hb0.le
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  constructor
  · have hb0' := (norm_blkAt_le _ 0 0).trans hT
    rw [blkAt_sub, bl0, blkAt_add, hP0, zero_add, hS0, hGs0] at hb0'
    have e : blkAt T 0 0 - sOne b E X • (mOf b E X * (mOf b E X)ᴴ) =
        (blkAt T 0 0 - mOf b E X * (sOne b E X • G0ᴴ)) +
          mOf b E X * (sOne b E X • (G0ᴴ - (mOf b E X)ᴴ)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, smul_sub]; abel
    have hs' : sOne b E X = ((1 - 2 * b : ℝ) : ℂ) * tTwo b E X 0 + (b : ℂ) * tTwo b E X 1 := rfl
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * (Cf * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add (by rw [hs']; exact hb0') ?_
          refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul hs ?_ (norm_nonneg _) hCf)
          rw [norm_conjTranspose_sub]; exact hE0
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * (Cf * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * Cf * CD) / (W : ℝ) ^ 2 by ring]
          have : 0 ≤ CD * (1 + b * Cw) * CD := by positivity
          exact div_le_div_of_nonneg_right (by linarith) hW2
  · have hb1 := (norm_blkAt_le _ 1 1).trans hT
    rw [blkAt_sub, bl1, blkAt_add, hP1, hS1, hGs1] at hb1
    have e0 : G1ᴴ + ((b : ℂ) * tTwo b E X 0) • G1ᴴ = (1 + (b : ℂ) * tTwo b E X 0) • G1ᴴ := by
      rw [add_smul, one_smul]
    rw [e0] at hb1
    have e : blkAt T 1 1 - (vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X)) • 1 =
        (blkAt T 1 1 - vOf b E X • ((1 + (b : ℂ) * tTwo b E X 0) • G1ᴴ)) +
          vOf b E X • ((1 + (b : ℂ) * tTwo b E X 0) • (G1ᴴ - (vOf b E X • 1)ᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_one, smul_sub, smul_sub, smul_smul, smul_smul]
      simp only [Complex.star_def, smul_smul, mul_assoc]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) := by
          refine add_le_add hb1 ?_
          refine (norm_smul_le _ _).trans (mul_le_mul hv ?_ (norm_nonneg _) hCD)
          refine (norm_smul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
          · calc ‖1 + (b : ℂ) * tTwo b E X 0‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * tTwo b E X 0‖ :=
                  norm_add_le _ _
              _ ≤ 1 + b * Cw := by rw [norm_one]; linarith
          · rw [norm_conjTranspose_sub]; exact hE1
      _ ≤ _ := by
          rw [show Cu / (W : ℝ) ^ 2 + CD * ((1 + b * Cw) * (CD / (W : ℝ) ^ 2)) =
            (Cu + CD * (1 + b * Cw) * CD) / (W : ℝ) ^ 2 by ring]
          gcongr
          have : 0 ≤ CD * Cf * CD := by positivity
          linarith

/-- **The scalar system for `s₁`**: `t₁ = s₁A`, `t₂ = h(1 + bt₁)`, `s₁(1 - k_hA) = bh`, each up
to `C/W²`. -/
theorem scalarS1_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖tTwo b E X 0 - sOne b E X * aOf b E X‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)‖ ≤ C / (W : ℝ) ^ 2 ∧
        ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := scalarS1_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  refine ⟨((1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1) * C₁, max (max W₁ WD) Ww, by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWD⟩, hWw⟩ := hW
  obtain ⟨hW1, -, -, hv, -⟩ := hD W hWD E hE X hX
  obtain ⟨hb00, hb11⟩ := hB W hW₁ E hE X hX
  have hent := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![0, 2] ![1, SourceMixing.pTwo, 1] norm_ins_le).1
  have hent' : ∀ α β, Integrable (fun ω => (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :
      LayerMat W) α β) (layerLaw W b .oneBlockOnePort) := fun α β => by
    have h := hent α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, SourceMixing.pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h; exact h
  have ht : ∀ r, tTwo b E X r = blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ))) r := fun r => integral_blkTr _ hent' r
  have d1 : ‖tTwo b E X 0 - sOne b E X * aOf b E X‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_smul, smul_eq_mul, mul_left_comm, ← ht] at h
    exact h
  have d2 : ‖tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 1 _).trans hb11
    rw [normTrace_smul_one hW1, ← ht] at h
    have e : vOf b E X * (1 + (b : ℂ) * tTwo b E X 0) * conj (vOf b E X) =
        hOf b E X * (1 + (b : ℂ) * tTwo b E X 0) := by unfold hOf; ring
    rw [e] at h; exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hfac : 1 ≤ (1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1 := by nlinarith [mul_nonneg hCD hCD]
  have hup : C₁ / (W : ℝ) ^ 2 ≤ ((1 - 2 * b) + b + b ^ 2 * (CD * CD) + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ hfac) hW2'.le
  refine ⟨d1.trans hup, d2.trans hup, ?_⟩
  have hh : ‖hOf b E X‖ ≤ CD * CD := by
    unfold hOf; rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have e : sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X =
      ((1 - 2 * b : ℝ) : ℂ) * (tTwo b E X 0 - sOne b E X * aOf b E X) +
        (b : ℂ) * (tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)) +
        (b : ℂ) ^ 2 * hOf b E X * (tTwo b E X 0 - sOne b E X * aOf b E X) := by
    unfold khOf; rw [show sOne b E X = ((1 - 2 * b : ℝ) : ℂ) * tTwo b E X 0 +
      (b : ℂ) * tTwo b E X 1 from rfl]; ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (tTwo b E X 0 - sOne b E X * aOf b E X)‖ +
        ‖(b : ℂ) * (tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0))‖ +
        ‖(b : ℂ) ^ 2 * hOf b E X * (tTwo b E X 0 - sOne b E X * aOf b E X)‖ :=
        norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) =
            ((1 - 2 * b) + b + b ^ 2 * (CD * CD)) * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.LengthUniform
