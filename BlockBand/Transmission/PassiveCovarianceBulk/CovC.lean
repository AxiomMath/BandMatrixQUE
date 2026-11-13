module

public import BlockBand.Transmission.PassiveCovarianceBulk.SdQExpand
public import BlockBand.Transmission.PassiveCovariance.CovC1
public import BlockBand.Transmission.PassiveCovariance.CovC2

/-!
# Bulk-uniform crossed covariances

The covariance as `E[P·Q⁰]` and the crossed sources `X₁`, `X₂` of the Level-0 covariance,
with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- `L²` of dressed forms, uniformly over passive inputs.
Bulk-uniform copy of `memLp_wordForm_unif` (constants uniform on `bulkInterval κ`). -/
theorem memLp_wordForm_unif_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ a c : LayerSite W .oneBlockOnePort → ℂ,
        MemLp (fun ω => wordForm (kHat b E X) a c wd D (gRes b E X ω)) 2
          (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hP⟩ := memLp_poly_bulk hA hb0 hb hκ (Lw + 1)
  refine ⟨W₀, fun W hW E hEκ X hX ℓ hℓ wd D hD a c => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  exact hP W hW E hEκ X hX _ (measurable_wordForm _ a c wd D
    (measurable_layerRes E (boundaryZ b E) X)).aestronglyMeasurable _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1

/-- **The covariance as `E[P·Q⁰]`.**
Bulk-uniform copy of `cov_eq_form` (constants uniform on `bulkInterval κ`). -/
theorem cov_eq_form_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        let μ := layerLaw W b .oneBlockOnePort
        let Q := fun ω => wordForm (kHat b E X) (physVec v₃) (physVec v₄) ![1, 3]
          ![1, portProj, 1] (gRes b E X ω)
        bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ =
          ∫ ω, wordForm (kHat b E X) (physVec v₁) (physVec v₂) ![1, 3] ![1, portProj, 1]
            (gRes b E X ω) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ := by
  obtain ⟨W₀, hm⟩ := memLp_wordForm_unif_bulk hA hb0 hb hκ 2 1
  refine ⟨W₀, fun W hW E hEκ X hX v₁ v₂ v₃ v₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Q
  set P := fun ω => wordForm (kHat b E X) (physVec v₁) (physVec v₂) ![1, 3] ![1, portProj, 1]
    (gRes b E X ω)
  have hU : ∀ i j, Integrable (fun ω => freshU b E X ω i j) μ := fun i j => by
    have e : ∀ ω, freshU b E X ω i j = wordForm (kHat b E X) (physVec (Pi.single i 1))
        (physVec (Pi.single j 1)) ![1, 3] ![1, portProj, 1] (gRes b E X ω) := fun ω => by
      rw [← freshU_wordForm]; simp [bilinear, dotProduct, mulVec, Pi.single_apply]
    simp only [e]
    exact (hm W hW E hEκ X hX 2 le_rfl _ _ norm_uIns_le _ _).integrable one_le_two
  have hb' : ∀ (u v : Fin W → ℂ) ω,
      bilinear u (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)) v =
      wordForm (kHat b E X) (physVec u) (physVec v) ![1, 3] ![1, portProj, 1] (gRes b E X ω) -
        ∫ ω', wordForm (kHat b E X) (physVec u) (physVec v) ![1, 3] ![1, portProj, 1]
          (gRes b E X ω') ∂freshLaw W b := fun u v ω => by
    rw [bilinear_sub, bilinear_matrixExpect (μ := freshLaw W b) _ _ _ hU]
    simp only [freshU_wordForm]
  have hP2 : MemLp P 2 μ := by
    have := hm W hW E hEκ X hX 2 le_rfl ![1, 3] ![1, portProj, 1] norm_uIns_le (physVec v₁) (physVec v₂)
    exact this
  have hQ2 : MemLp Q 2 μ := hm W hW E hEκ X hX 2 le_rfl ![1, 3] ![1, portProj, 1] norm_uIns_le _ _
  have hQc : MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂μ) 2 μ := hQ2.sub (memLp_const _)
  unfold bilinearCovariance
  simp only [hb']
  change ∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ = _
  have i1 : Integrable (fun ω => P ω * (Q ω - ∫ ω', Q ω' ∂μ)) μ := hP2.integrable_mul hQc
  have i2 : Integrable (fun ω => (∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ)) μ :=
    (hQc.integrable one_le_two).const_mul _
  simp_rw [sub_mul (P _)]
  rw [integral_sub i1 i2,
    integral_const_mul, integral_sub (hQ2.integrable one_le_two) (integrable_const _),
    integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero]

/-- **The crossed source `X₁`.**
Bulk-uniform copy of `cov_C1` (constants uniform on `bulkInterval κ`). -/
theorem cov_C1_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₂ * vecNorm v₃ ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let xc := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₁
        let Q := fun ω => wordForm Kh (physVec v₃) (physVec v₄) ![1, 3] ![1, portProj, 1]
          (gRes b E X ω)
        let F := fun ω => star xc ⬝ᵥ (wordGamma Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0 *ᵥ
          physVec v₂)
        let τ := ∑ q : Fin 2, sRow b q * ∫ ω, SourceMixing.blkTr (gSide b E X false ω *
          wordAlpha Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0) q ∂μ
        let X₁ := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
          ((∫ ω, star xc ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
              physVec v₄) ∂μ) *
            ∫ ω, star (physVec v₃) ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
              bProj p' * (gSide b E X false ω * wordVal Kh (gRes b E X ω) ![3] ![portProj, 1])) *ᵥ
              physVec v₂) ∂μ)
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            τ * ∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ - X₁‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm xc * vecNorm v₄) := by
  obtain ⟨C, W₁, hC, hs⟩ := sdQ_expand_bulk hP hA hb0 hb hκ 2 1 false
  obtain ⟨W₂, hcov⟩ := cov_eq_form_bulk hA hb0 hb hκ
  obtain ⟨CD, W₃, hDI⟩ := dressed_inverse_bulk hA hb0 hb hκ
  refine ⟨C, max (max W₁ W₂) (max W₃ 1), hC, fun W hW E hEκ X hX v₁ v₂ v₃ v₄ hn => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Kh xc Q F τ X₁
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW1' : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hxc : IsPhys xc := isPhys_conjT_mulVec (kHat_mbar_blk b E X hW1' (hDI W hW3 E hEκ X hX).1)
    (isPhys_physVec v₁)
  have h := hs W hW1 E hEκ X hX 1 (by norm_num) ![3] ![portProj, 1] norm_nIns_le 2 le_rfl ![1, 3]
    ![1, portProj, 1] norm_uIns_le Kh (physVec v₁) (physVec v₂) (physVec v₃) (physVec v₄)
    (by rw [vecNorm_physVec, vecNorm_physVec]; exact hn)
  simp only at h
  have eL : ∫ ω, star (physVec v₁) ⬝ᵥ ((kHat b E X * gSide b E X false ω *
      wordVal (kHat b E X) (gRes b E X ω) ![3] ![portProj, 1]) *ᵥ physVec v₂) *
      (Q ω - ∫ ω', Q ω' ∂μ) ∂μ = bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ := by
    have e := fun ω => word_P_eq b E X ω (physVec v₁) (physVec v₂)
    simp only [e]
    exact (hcov W hW2 E hEκ X hX.posSemidef v₁ v₂ v₃ v₄).symm
  have eM : ∫ ω, star (physVec v₁) ⬝ᵥ ((kHat b E X * mbarSide b E X false *
      wordVal (kHat b E X) (gRes b E X ω) ![3] ![portProj, 1]) *ᵥ physVec v₂) *
      (Q ω - ∫ ω', Q ω' ∂μ) ∂μ = 0 := by
    have e : ∀ ω, star (physVec v₁) ⬝ᵥ ((kHat b E X * mbarSide b E X false *
        wordVal (kHat b E X) (gRes b E X ω) ![3] ![portProj, 1]) *ᵥ physVec v₂) *
        (Q ω - ∫ ω', Q ω' ∂μ) = 0 := fun ω => by
      rw [wordVal_N, ← mulVec_mulVec, star_form_eq, form_portProj_eq_zero hxc, zero_mul]
    simp only [e, integral_zero]
  have eJ : ∑ j : Fin 1, ∑ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X false ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] j) q ∂μ) *
      ∫ ω, star xc ⬝ᵥ ((dRow b q * wordGamma (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] j) *ᵥ
        physVec v₂) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ = τ * ∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ := by
    rw [Fin.sum_univ_one]
    simp only [form_dRow _ hxc, mul_assoc, integral_const_mul]
    simp only [τ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [eL, eM, eJ, sub_zero, vecNorm_physVec] at h
  exact h

/-- **The crossed source `X₂`.**
Bulk-uniform copy of `cov_C2` (constants uniform on `bulkInterval κ`). -/
theorem cov_C2_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        vecNorm ((kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁) * vecNorm v₄ ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let xc := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₁
        let xc' := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₂
        let Q := fun ω => wordForm Kh (physVec v₃) (physVec v₄) ![1, 3] ![1, portProj, 1]
          (gRes b E X ω)
        let F := fun ω => star xc ⬝ᵥ (wordGamma Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0 *ᵥ
          physVec v₂)
        let X₂ := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
          ((∫ ω, star xc' ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
              physVec v₃) ∂μ) *
            ∫ ω, star (physVec v₄) ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
              bProj p' * (gSide b E X false ω * wordVal Kh (gRes b E X ω) ![] ![1])) *ᵥ xc) ∂μ)
        ‖∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ - conj X₂‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm xc' * vecNorm v₃) := by
  obtain ⟨C, W₁, hC, hs⟩ := sdQ_expand_bulk hP hA hb0 hb hκ 2 1 false
  obtain ⟨W₂, hm⟩ := memLp_wordForm_unif_bulk hA hb0 hb hκ 2 1
  refine ⟨C, max W₁ W₂, hC, fun W hW E hEκ X hX v₁ v₂ v₃ v₄ hn => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Kh xc xc' Q F X₂
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_max_right _ _) hW
  have hD1 : ∀ j, ‖(![1] : Fin 1 → LayerMat W) j‖ ≤ 1 := fun j => by
    fin_cases j; exact norm_one_matrix_le
  have h := hs W hW1 E hEκ X hX 0 (by norm_num) ![] ![1] hD1 2 le_rfl ![1, 3] ![1, portProj, 1]
    norm_uIns_le Kh (physVec v₂) xc (physVec v₄) (physVec v₃)
    (by rw [vecNorm_physVec]; exact hn)
  simp only at h
  set Qt := fun ω => wordForm Kh (physVec v₄) (physVec v₃) ![1, 3] ![1, portProj, 1] (gRes b E X ω)
  have hQt : Integrable Qt μ :=
    (hm W hW2 E hEκ X hX.posSemidef 2 le_rfl _ _ norm_uIns_le _ _).integrable one_le_two
  have eL : ∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ =
      conj (∫ ω, star (physVec v₂) ⬝ᵥ ((kHat b E X * gSide b E X false ω *
        wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ) := by
    rw [← integral_conj]
    have e : ∀ ω, conj (star (physVec v₂) ⬝ᵥ ((kHat b E X * gSide b E X false ω *
        wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ)) =
        F ω * (Q ω - ∫ ω', Q ω' ∂μ) := fun ω => by
      have q1 : ∀ ω, conj (Qt ω) = Q ω := fun ω => conj_Q _ _ _ _
      rw [map_mul, map_sub, ← integral_conj, ← conj_F, Complex.conj_conj]
      simp only [q1]
      rfl
    simp only [e]
  have eM : ∫ ω, star (physVec v₂) ⬝ᵥ ((kHat b E X * mbarSide b E X false *
      wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ = 0 := by
    have e : ∀ ω, wordVal (kHat b E X) (gRes b E X ω) ![] ![1] = 1 := fun ω => by
      simp [wordVal_zero]
    simp only [e]
    rw [integral_const_mul, integral_sub hQt (integrable_const _), integral_const, probReal_univ,
      one_smul, sub_self, mul_zero]
  have eJ : ∑ j : Fin 0, ∑ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X false ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 0 ![] ![1] j) q ∂μ) *
      ∫ ω, star xc' ⬝ᵥ ((dRow b q * wordGamma (kHat b E X) (gRes b E X ω) 0 ![] ![1] j) *ᵥ
        xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ = 0 := Fin.sum_univ_zero _
  rw [eM, eJ, sub_zero, sub_zero, vecNorm_physVec] at h
  rw [eL, ← map_sub, Complex.norm_conj]
  exact h

end BlockBand.Transmission.CovarianceBulk
