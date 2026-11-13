module

public import BlockBand.Transmission.PassiveCovarianceBulk.AlpBlocks
public import BlockBand.Transmission.PassiveCovariance.GsFirst
public import BlockBand.Transmission.PassiveCovariance.AdjBlock

/-!
# Bulk-uniform `𝒢ᴴ`-first means

The `𝒢ᴴ`-first mean and the `𝒢ᴴ`-first expansion on the physical block, with constants and `W₀`
uniform in `E ∈ bulkInterval κ`.
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

/-- **The `𝒢ᴴ`-first mean, physical block.**
Bulk-uniform copy of `gsMean_block` (constants uniform on `bulkInterval κ`). -/
theorem gsMean_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0 -
          rB b E X p • ((SourceMixing.mOf b E X)ᴴ *
            blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cs, Ws, hCs, hS⟩ := sdOne_expand_bulk hA hb0 hb hκ 1 1 true
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 2 1
  refine ⟨Cs * CD, max (max Ws WD) (max WK Ww), by positivity, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWD⟩, hWK, hWw⟩ := hW
  obtain ⟨hW1, -, hM, -, -, -, -, -, hG, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨hU, -, -, -⟩ := hK W hWK E hEκ X hX
  obtain ⟨m00, m01⟩ := mbarTrue_blk hW1 hU
  set μ := layerLaw W b .oneBlockOnePort
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set M := SourceMixing.mOf b E X
  have hent : ∀ α β, Integrable
      (fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw E hEκ X hX.posSemidef 2 le_rfl ![2, 0] (dP3 p) (norm_dP3_le p)).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dP3 p) α β) =
        fun ω => ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dP3, wLetter]
    rw [e] at h; exact h
  refine ⟨hent, ?_⟩
  have hPG : ∀ α β, Integrable (fun ω => (bProj p * gRes b E X ω : LayerMat W) α β) μ :=
    fun α β => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hG k β).const_mul _
  refine opNorm_le_of_bilinear _ (by positivity) fun u v => ?_
  have h := hS W hWs E hEκ X hX 1 le_rfl ![0] (dP p) (norm_dP_le p) 1 (physVec u) (physVec v)
  simp only at h
  -- the vector `x̌ = D⁻¹ι₁u = ι₁(Mu)`
  have hxc : (1 * mbarSide b E X true)ᴴ *ᵥ physVec u = physVec (M *ᵥ u) := by
    rw [Matrix.one_mul, conjT_mulVec_physVec m01, m00, conjTranspose_conjTranspose]
  rw [hxc] at h
  -- first term
  have e1 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * gSide b E X true ω *
      wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ (((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) *ᵥ physVec v) :=
    fun ω => by rw [wordVal_PpG, Matrix.one_mul]; rfl
  simp only [e1] at h
  rw [integral_form _ hent] at h
  -- second term
  have e2 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * mbarSide b E X true *
      wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ ((mbarSide b E X true * (bProj p * gRes b E X ω)) *ᵥ physVec v) :=
    fun ω => by rw [wordVal_PpG, Matrix.one_mul]
  simp only [e2] at h
  have hMPG : ∀ α β, Integrable
      (fun ω => (mbarSide b E X true * (bProj p * gRes b E X ω) : LayerMat W) α β) μ :=
    fun α β => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun k _ => (hPG k β).const_mul _
  rw [integral_form _ hMPG, ← SourceMixing.mul_matrixExpect' _ _ hPG,
    ← SourceMixing.mul_matrixExpect' _ _ hG, blkAt_mul, Fin.sum_univ_two, m00, m01,
    Matrix.zero_mul, add_zero, blkAt_bProj_mul] at h
  -- third term
  have e3 : ∀ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X true ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) q ∂μ) = tP b E X q p := fun q => by
    have e : ∀ ω, SourceMixing.blkTr (gSide b E X true ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) q =
        SourceMixing.blkTr (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) p := fun ω => by
      rw [wordAlpha_PpG]; exact blkTr_cyc _ p q
    simp only [e]; rfl
  have e4 : ∀ q : Fin 2, (∫ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
      wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) *ᵥ physVec v) ∂μ) =
      sRow b q * bilinear u (Mᴴ * G0) v := fun q => by
    have e : ∀ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
        wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) *ᵥ physVec v) =
        sRow b q * star (physVec (M *ᵥ u)) ⬝ᵥ (gRes b E X ω *ᵥ physVec v) := fun ω => by
      rw [wordGamma_PpG]; exact form_dRow q (isPhys_physVec _) _ _
    simp only [e]
    rw [integral_const_mul, integral_form _ hG, ← bilinear_conjT_left, conjTranspose_conjTranspose]
  rw [Fin.sum_univ_one, Fin.sum_univ_two, e3, e3, e4, e4] at h
  rw [vecNorm_physVec, vecNorm_physVec] at h
  -- assemble
  have hrB : rB b E X p = ind 0 p + (sRow b 0 * tP b E X 0 p + sRow b 1 * tP b E X 1 p) := by
    rw [sRow_zero, sRow_one]; simp only [rB, sig1]; push_cast; ring
  have eq : bilinear u (blkAt (matrixExpect μ
      (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0 - rB b E X p • (Mᴴ * G0)) v =
      bilinear u (blkAt (matrixExpect μ
        (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) 0 0) v -
      bilinear u (Mᴴ * (ind 0 p • G0)) v -
      (tP b E X 0 p * (sRow b 0 * bilinear u (Mᴴ * G0) v) +
        tP b E X 1 p * (sRow b 1 * bilinear u (Mᴴ * G0) v)) := by
    rw [bilinear_sub, bilinear_smul, Matrix.mul_smul, bilinear_smul, hrB]
    change _ = _ - (if (0 : Fin 2) = p then (1 : ℂ) else 0) * _ - _
    simp only [ind]; ring
  rw [eq]
  have hMu : vecNorm (M *ᵥ u) ≤ CD * vecNorm u := (vecNorm_mulVec_le M u).trans
    (mul_le_mul_of_nonneg_right hM (vecNorm_nonneg u))
  refine h.trans ?_
  have := vecNorm_nonneg v
  calc Cs / (W : ℝ) ^ 2 * (vecNorm (M *ᵥ u) * vecNorm v) ≤
      Cs / (W : ℝ) ^ 2 * (CD * vecNorm u * vecNorm v) := by gcongr
    _ = _ := by ring

/-- **The `𝒢ᴴ`-first expansion, physical block.**
Bulk-uniform copy of `adjBlock` (constants uniform on `bulkInterval κ`). -/
theorem adjBlock_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
      (∀ α β, Integrable (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D α β)
        (layerLaw W b .oneBlockOnePort)) →
      (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D) α β)
        (layerLaw W b .oneBlockOnePort)) →
      (∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j α β)
        (layerLaw W b .oneBlockOnePort)) →
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 -
          (SourceMixing.mOf b E X)ᴴ *
            (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0 +
            ∑ j, sig1 b
                (trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0)
                (trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cs, Ws, hCs, hS⟩ := sdOne_expand_bulk hA hb0 hb hκ Lw Kd true
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  refine ⟨Cs * CD, max (max Ws WD) WK, by positivity,
    fun W hW E hEκ X hX ℓ hℓ wd D hDn hI hI' hIγ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWD⟩, hWK⟩ := hW
  obtain ⟨hW1, -, hM, -, -, -, -, -, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨hU, -, -, -⟩ := hK W hWK E hEκ X hX
  obtain ⟨m00, m01⟩ := mbarTrue_blk hW1 hU
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  refine opNorm_le_of_bilinear _ (by positivity) fun u v => ?_
  have h := hS W hWs E hEκ X hX ℓ hℓ wd D hDn 1 (physVec u) (physVec v)
  simp only at h
  have hxc : (1 * mbarSide b E X true)ᴴ *ᵥ physVec u = physVec (M *ᵥ u) := by
    rw [Matrix.one_mul, conjT_mulVec_physVec m01, m00, conjTranspose_conjTranspose]
  rw [hxc] at h
  have e1 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * gSide b E X true ω *
      wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ (((gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ
        physVec v) := fun ω => by rw [Matrix.one_mul]; rfl
  simp only [e1] at h
  rw [integral_form _ hI'] at h
  have e2 : ∀ ω, star (physVec u) ⬝ᵥ ((1 * mbarSide b E X true *
      wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ physVec v) =
      star (physVec u) ⬝ᵥ ((mbarSide b E X true * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ
        physVec v) := fun ω => by rw [Matrix.one_mul]
  simp only [e2] at h
  have hMN : ∀ α β, Integrable
      (fun ω => (mbarSide b E X true * wordVal (kHat b E X) (gRes b E X ω) wd D : LayerMat W) α β)
      μ := fun α β => by
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hI k β).const_mul _
  rw [integral_form _ hMN, ← SourceMixing.mul_matrixExpect' _ _ hI, blkAt_mul, Fin.sum_univ_two,
    m00, m01, Matrix.zero_mul, add_zero] at h
  have e4 : ∀ (j : Fin ℓ) (q : Fin 2), (∫ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
      wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ physVec v) ∂layerLaw W b .oneBlockOnePort) =
      sRow b q * bilinear u (Mᴴ * blkAt (matrixExpect μ
        (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0) v := fun j q => by
    have e : ∀ ω, star (physVec (M *ᵥ u)) ⬝ᵥ ((dRow b q *
        wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ physVec v) =
        sRow b q * star (physVec (M *ᵥ u)) ⬝ᵥ
          (wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j *ᵥ physVec v) := fun ω =>
      form_dRow q (isPhys_physVec _) _ _
    simp only [e]
    rw [integral_const_mul, integral_form _ (hIγ j), ← bilinear_conjT_left,
      conjTranspose_conjTranspose]
  simp only [e4, Fin.sum_univ_two] at h
  rw [vecNorm_physVec, vecNorm_physVec] at h
  set Y := blkAt (matrixExpect μ
    (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0
  set N0 := blkAt (matrixExpect μ (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)) 0 0
  set Γ := fun j => blkAt (matrixExpect μ
    (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)) 0 0
  set r := fun (j : Fin ℓ) (q : Fin 2) =>
    trMean b (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) q
  have eq : bilinear u (Y - Mᴴ * (N0 + ∑ j, sig1 b (r j 0) (r j 1) • Γ j)) v =
      bilinear u Y v - bilinear u (Mᴴ * N0) v -
        ∑ j, (r j 0 * (sRow b 0 * bilinear u (Mᴴ * Γ j) v) +
          r j 1 * (sRow b 1 * bilinear u (Mᴴ * Γ j) v)) := by
    rw [bilinear_sub, Matrix.mul_add, bilinear_add, Matrix.mul_sum, bilinear_finsum,
      sub_add_eq_sub_sub]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, bilinear_smul, sRow_zero, sRow_one]
    simp only [sig1]; push_cast; ring
  rw [eq]
  have hMu : vecNorm (M *ᵥ u) ≤ CD * vecNorm u := (vecNorm_mulVec_le M u).trans
    (mul_le_mul_of_nonneg_right hM (vecNorm_nonneg u))
  refine (h.trans ?_)
  have := vecNorm_nonneg v
  calc Cs / (W : ℝ) ^ 2 * (vecNorm (M *ᵥ u) * vecNorm v) ≤
      Cs / (W : ℝ) ^ 2 * (CD * vecNorm u * vecNorm v) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.CovarianceBulk
