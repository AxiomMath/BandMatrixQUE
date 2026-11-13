module

public import BlockBand.Transmission.SourceMixing.PassiveMeanBlock
public import BlockBand.Transmission.LengthUniform.BulkDressed
public import BlockBand.Transmission.LengthUniform.BulkMeanExpansion
public import BlockBand.Transmission.LengthUniform.BulkWordMean

/-!
# Bulk-uniform weighted expansion and the two-resolvent mean

The weighted mean-field expansion, the two-resolvent weighted equation and the passive mean
`‖E[LL*] - s₁·KM(KM)ᴴ‖ ≤ C/W²`, uniformly in `E ∈ bulkInterval κ`: the constants and `W₀` depend
only on `b`, the bulk margin `κ`.
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
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The weighted mean-field expansion.** -/
theorem weightedExpansion_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) -
          kHat b E X * (dressed b E X)⁻¹ *
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
  obtain ⟨hU, -, hKD, -⟩ := hK W (le_trans (le_max_right _ _) hW) E hE X hX
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
  have e : kHat b E X * T - kHat b E X * (dressed b E X)⁻¹ * R =
      kHat b E X * (dressed b E X)⁻¹ * (dressed b E X * T - R) := by
    rw [Matrix.mul_sub]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (kHat b E X), hDinvD, Matrix.mul_one]
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
  calc _ ≤ ‖kHat b E X * (dressed b E X)⁻¹‖ * ‖dressed b E X * T - R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ CK * (Ce / (W : ℝ) ^ 2) := mul_le_mul hKD he' (norm_nonneg _) hCK
    _ = _ := by ring

/-- **The two-resolvent weighted equation** (`w = P₂(K̂𝒢)ᴴ`). -/
theorem twoResolvent_weighted_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ)) -
          kHat b E X * (dressed b E X)⁻¹ *
            (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ) +
              selfEnergy b
                (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) 0 ∂layerLaw W b .oneBlockOnePort)
                (∫ ω, blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) 1 ∂layerLaw W b .oneBlockOnePort) *
              matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => (kHat b E X * gRes b E X ω)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, hC, h⟩ := weightedExpansion_bulk hA hb0 hb hκ 1 1
  refine ⟨C, W₀, hC, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have := h W hW E hE X hX 1 le_rfl wdStar dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at this
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordVal_star]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => SourceMixing.pTwo * (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_star]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) r :=
    fun r => funext fun ω => by rw [wordAlpha_star]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_star]
  rw [e1, e2, e3 0, e3 1, e4] at this
  exact this

/-- **Block extraction of the passive mean**: `‖E[LL*] - s₁·KM(KM)ᴴ‖ ≤ C/W²`, with the
bounds `‖KM‖ ≤ C`, `|s₁| ≤ C`. -/
theorem freshU_mean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖kmOf b E X‖ ≤ C ∧ ‖sOne b E X‖ ≤ C ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X) -
          sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hT⟩ := twoResolvent_weighted_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  obtain ⟨CD, WD, -, hres⟩ := mean_residuals_bulk hA hb0 hb hκ
  set Cs := (1 - 2 * b) * Cw + b * Cw
  have hCs : 0 ≤ Cs := by have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  refine ⟨max (max CK Cs) (C₁ + Cs * CK * CK), max (max W₁ WK) (max Ww WD), by positivity,
    fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWK⟩, hWw, hWD⟩ := hW
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set D := dressed b E X
  obtain ⟨-, -, hKD, hKE⟩ := hK W hWK E hE X hX
  obtain ⟨-, -, -, -, -, -, e01, -⟩ := hres W hWD E hE X hX
  have hKM : ‖kmOf b E X‖ ≤ CK := (norm_blkAt_le _ _ _).trans hKD
  -- `|t_r| ≤ Cw`, `|s₁| ≤ Cs`
  have ht : ∀ r, ‖tTwo b E X r‖ ≤ Cw := fun r => by
    have h := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![0, 2] ![1, SourceMixing.pTwo, 1] norm_ins_le).2.2.2.2 r
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, SourceMixing.pTwo, 1]) r) =
        fun ω => blkTr (gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ)) r :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h
    exact h
  have hs : ‖sOne b E X‖ ≤ Cs := by
    unfold sOne
    have hb1 : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hb2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hb1, hb2]
    have : 0 ≤ 1 - 2 * b := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (ht 0) this)
      (mul_le_mul_of_nonneg_left (ht 1) hb0.le)
  refine ⟨hKM.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hs.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  -- integrability
  have hiN : ∀ α β, Integrable
      (fun ω => (gRes b E X ω * (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![0, 3] ![1, SourceMixing.pTwo, 1] norm_ins_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] ![1, SourceMixing.pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPKGstar]
    rw [e] at h
    exact h
  have hiG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ := fun α β => by
    have h := (hw W hWw E hE X hX.posSemidef 1 (by norm_num) ![0] ![1, 1] norm_ins1_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0] ![1, 1] α β) =
        fun ω => gRes b E X ω α β := funext fun ω => by rw [wordVal_G1]
    rw [e] at h
    exact h
  have hT' := hT W hW₁ E hE X hX
  set N := matrixExpect μ (fun ω => gRes b E X ω * (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ))
  set Ps := matrixExpect μ (fun ω => SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ) with hPsdef
  set S := (selfEnergy b (tTwo b E X 0) (tTwo b E X 1) : LayerMat W) with hSdef
  set Gs := matrixExpect μ (fun ω => (Kh * gRes b E X ω)ᴴ) with hGsdef
  -- (a) the left block
  have ha : blkAt (Kh * N) 0 0 = matrixExpect μ (freshU b E X) := by
    rw [mul_matrixExpect' _ _ hiN, blkAt_matrixExpect]
    exact congrArg (matrixExpect μ) (funext fun ω => blkAt_freshU b E X ω)
  -- (b) the right block
  have hKD01 : blkAt (Kh * D⁻¹) 0 1 = 0 := by
    rw [(blkAt_kHat_mul_zero b E X D⁻¹).2, e01, Matrix.mul_zero]
  have hPs : blkAt Ps 0 0 = 0 := by
    have e : (fun ω => blkAt (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [hPsdef, blkAt_matrixExpect, e]
    ext x y; simp [matrixExpect]
  obtain ⟨hS00, hS01⟩ := blkAt_selfEnergy (W := W) b (tTwo b E X 0) (tTwo b E X 1)
  have hGs : blkAt Gs 0 0 = (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ := by
    rw [hGsdef, matrixExpect_conjTranspose, blkAt_conjTranspose, mul_matrixExpect' _ _ hiG]
  have hb : blkAt (Kh * D⁻¹ * (Ps + S * Gs)) 0 0 =
      kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ) := by
    have hSG : blkAt (S * Gs) 0 0 = sOne b E X • blkAt Gs 0 0 := by
      rw [blkAt_mul, Fin.sum_univ_two, hSdef, hS00, hS01, Matrix.zero_mul, add_zero,
        Matrix.smul_mul, Matrix.one_mul]
      rfl
    rw [blkAt_mul, Fin.sum_univ_two, hKD01, Matrix.zero_mul, add_zero, blkAt_add, hPs, zero_add,
      hSG, hGs]
    rfl
  -- assemble
  have hblk : ‖matrixExpect μ (freshU b E X) -
      kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ)‖ ≤
        C₁ / (W : ℝ) ^ 2 := by
    rw [← ha, ← hb, ← blkAt_sub]
    exact (norm_blkAt_le _ _ _).trans hT'
  have hdiff : ‖blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0 - kmOf b E X‖ ≤ CK / (W : ℝ) ^ 2 := by
    rw [kmOf, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hKE
  have e : matrixExpect μ (freshU b E X) - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ) =
      (matrixExpect μ (freshU b E X) -
        kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ)) +
      sOne b E X • (kmOf b E X * (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0 - kmOf b E X)ᴴ) := by
    rw [Matrix.mul_smul, conjTranspose_sub, Matrix.mul_sub, smul_sub]; abel
  rw [e]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  calc _ ≤ C₁ / (W : ℝ) ^ 2 + ‖sOne b E X‖ * (‖kmOf b E X‖ * (CK / (W : ℝ) ^ 2)) := by
        refine (norm_add_le _ _).trans (add_le_add hblk ?_)
        refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [Matrix.l2_opNorm_conjTranspose]; exact hdiff
    _ ≤ C₁ / (W : ℝ) ^ 2 + Cs * (CK * (CK / (W : ℝ) ^ 2)) := by gcongr
    _ = (C₁ + Cs * CK * CK) / (W : ℝ) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hW2

end BlockBand.Transmission.LengthUniform
