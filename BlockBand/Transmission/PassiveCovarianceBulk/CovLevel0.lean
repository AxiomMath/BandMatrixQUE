module

public import BlockBand.Transmission.PassiveCovarianceBulk.CovC
public import BlockBand.Transmission.PassiveCovariance.CovLevel0
public import BlockBand.Transmission.LengthUniform.BulkWeighted

/-!
# Bulk-uniform Level-0 covariance

The covariance `Cov(v₁*Uv₂, v₃*Uv₄)` equals `τ̄·conj X₂ + X₁` up to `C/W²`, with constants and `W₀`
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

/-- `|τ̄| ≤ C_τ`.
Bulk-uniform copy of `norm_tau_le` (constants uniform on `bulkInterval κ`). -/
theorem norm_tau_le_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
        ‖∑ q : Fin 2, sRow b q * ∫ ω, SourceMixing.blkTr (gSide b E X false ω *
          wordAlpha (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q
            ∂layerLaw W b .oneBlockOnePort‖ ≤ C := by
  obtain ⟨C₃, W₃, hC₃, hm⟩ := norm_integral_poly_le_bulk hA hb0 hb hκ 2
  refine ⟨2 * C₃, W₃, by positivity, fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hq : ∀ q : Fin 2, ‖∫ ω, SourceMixing.blkTr (gSide b E X false ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q
        ∂layerLaw W b .oneBlockOnePort‖ ≤ 1 * C₃ := fun q => by
    refine hm W hW E hEκ X hX _ 1 2 le_rfl fun ω => ?_
    rw [wordAlpha_N, one_mul]
    refine (SourceMixing.norm_blkTr_le _ q).trans ?_
    have hG := norm_gRes_le_btFun b E X ω
    have hG0 := norm_nonneg (gRes b E X ω)
    calc ‖gSide b E X false ω * (portProj * (gRes b E X ω)ᴴ)‖
        ≤ ‖gSide b E X false ω‖ * (‖(portProj : LayerMat W)‖ * ‖(gRes b E X ω)ᴴ‖) :=
          (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1 + btFun b E X ω) * (1 * (1 + btFun b E X ω)) := by
          rw [norm_gSide, Matrix.l2_opNorm_conjTranspose]
          have := btFun_nonneg b E X ω
          exact mul_le_mul hG (mul_le_mul norm_portProj_le hG (norm_nonneg _) zero_le_one)
            (by positivity) (by positivity)
      _ = (1 + btFun b E X ω) ^ 2 := by ring
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q : Fin 2, ‖sRow b q * ∫ ω, SourceMixing.blkTr (gSide b E X false ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q
          ∂layerLaw W b .oneBlockOnePort‖ ≤ ∑ _q : Fin 2, 1 * (1 * C₃) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        exact mul_le_mul (norm_sRow_le hb0 hb q) (hq q) (norm_nonneg _) zero_le_one
    _ = 2 * C₃ := by simp

/-- **Level 0**: the covariance is an explicit bilinear expression in means.
Bulk-uniform copy of `cov_level0` (constants uniform on `bulkInterval κ`). -/
theorem cov_level0_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (ρ C : ℝ) (W₀ : ℕ), 0 < ρ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₁ ≤ ρ → vecNorm v₂ ≤ 1 →
        vecNorm v₃ ≤ 1 → vecNorm v₄ ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let xc := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₁
        let xc' := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₂
        let τ := ∑ q : Fin 2, sRow b q * ∫ ω, SourceMixing.blkTr (gSide b E X false ω *
          wordAlpha Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q ∂μ
        let X₁ := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
          ((∫ ω, star xc ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
              physVec v₄) ∂μ) *
            ∫ ω, star (physVec v₃) ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
              bProj p' * (gSide b E X false ω * wordVal Kh (gRes b E X ω) ![3] ![portProj, 1])) *ᵥ
              physVec v₂) ∂μ)
        let X₂ := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
          ((∫ ω, star xc' ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
              physVec v₃) ∂μ) *
            ∫ ω, star (physVec v₄) ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
              bProj p' * (gSide b E X false ω * wordVal Kh (gRes b E X ω) ![] ![1])) *ᵥ xc) ∂μ)
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - τ * conj X₂ - X₁‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C1, W1, hC1, hc1⟩ := cov_C1_bulk hP hA hb0 hb hκ
  obtain ⟨C2, W2, hC2, hc2⟩ := cov_C2_bulk hP hA hb0 hb hκ
  obtain ⟨Cτ, Wτ, hCτ, hτ⟩ := norm_tau_le_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  set K := max CK 1
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨K⁻¹, C1 + Cτ * (C2 * K), max (max W1 W2) (max Wτ WK), by positivity, by positivity,
    fun W hW E hEκ X hX v₁ v₂ v₃ v₄ hv₁ hv₂ hv₃ hv₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Kh xc xc' τ X₁ X₂
  have hW1 : W1 ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W2 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWτ : Wτ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWK : WK ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hKM : ‖(Kh * mbarSide b E X false)ᴴ‖ ≤ K := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact (hK W hWK E hEκ X hX).2.2.1.trans (le_max_left _ _)
  have hxc : vecNorm xc ≤ 1 := by
    refine (vecNorm_mulVec_le _ _).trans ?_
    rw [vecNorm_physVec]
    calc ‖(Kh * mbarSide b E X false)ᴴ‖ * vecNorm v₁ ≤ K * K⁻¹ :=
          mul_le_mul hKM hv₁ (vecNorm_nonneg _) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hxc' : vecNorm xc' ≤ K := by
    refine (vecNorm_mulVec_le _ _).trans ?_
    rw [vecNorm_physVec]
    calc ‖(Kh * mbarSide b E X false)ᴴ‖ * vecNorm v₂ ≤ K * 1 :=
          mul_le_mul hKM hv₂ (vecNorm_nonneg _) (by positivity)
      _ = K := mul_one _
  have h23 : vecNorm v₂ * vecNorm v₃ ≤ 1 := by
    have := vecNorm_nonneg v₂; nlinarith [vecNorm_nonneg v₃]
  have h44 : vecNorm xc * vecNorm v₄ ≤ 1 := by
    have := vecNorm_nonneg xc; nlinarith [vecNorm_nonneg v₄]
  have e1 := hc1 W hW1 E hEκ X hX v₁ v₂ v₃ v₄ h23
  have e2 := hc2 W hW2 E hEκ X hX v₁ v₂ v₃ v₄ h44
  have eτ : ‖τ‖ ≤ Cτ := hτ W hWτ E hEκ X hX.posSemidef
  simp only at e1 e2
  set I := ∫ ω, star xc ⬝ᵥ (wordGamma Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0 *ᵥ physVec v₂) *
    (wordForm Kh (physVec v₃) (physVec v₄) ![1, 3] ![1, portProj, 1] (gRes b E X ω) -
      ∫ ω', wordForm Kh (physVec v₃) (physVec v₄) ![1, 3] ![1, portProj, 1] (gRes b E X ω') ∂μ) ∂μ
  have halg : bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - τ * conj X₂ - X₁ =
      (bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - τ * I - X₁) +
        τ * (I - conj X₂) := by ring
  rw [halg]
  have hW0 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - τ * I - X₁‖ +
        ‖τ‖ * ‖I - conj X₂‖ := (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ C1 / (W : ℝ) ^ 2 * (1 * 1) + Cτ * (C2 / (W : ℝ) ^ 2 * (K * 1)) := by
        have hC1W : 0 ≤ C1 / (W : ℝ) ^ 2 := by positivity
        have hC2W : 0 ≤ C2 / (W : ℝ) ^ 2 := by positivity
        refine add_le_add (e1.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul hxc hv₄ (vecNorm_nonneg _) zero_le_one) hC1W))
          (mul_le_mul eτ (e2.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul hxc' hv₃ (vecNorm_nonneg _) (by positivity)) hC2W)) (norm_nonneg _) hCτ)
    _ = (C1 + Cτ * (C2 * K)) / (W : ℝ) ^ 2 := by ring

end BlockBand.Transmission.CovarianceBulk
