module

public import BlockBand.SourceProcess.FullSourceCovariance.CovExpand

/-!
# The four `Δ` main terms give the full-source covariance tensor

With `x_i = ι*v_i`, `y_i = Fv_i` (`FullSource.wardF`), the two equal-sign main terms
`(σ₋/W)(x₁*y₄)(x₃*y₂)` and `conj((σ₋/W)(x₂*y₃)(x₄*y₁))`, and the two opposite-sign main terms
`(σ₊/W)(x₁*x₄)(y₃*y₂)` and `(σ₊/W)(x₃*x₂)(y₁*y₄)`, sum to the tensor of the full-source
covariance lemma
`(D₀/2W)(P⊗P' + P'⊗P) - σ₋/(4η²W) P𝕊⊗P𝕊 - σ̄₋/(4η²W) 𝕊*P⊗𝕊*P` (`main_match`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate

variable {W : ℕ}

theorem bilinear_smul' {n : Type*} [Fintype n] (u v : n → ℂ) (c : ℂ) (M : Matrix n n ℂ) :
    bilinear u (c • M) v = c * bilinear u M v := by
  simp [bilinear, Matrix.smul_mulVec, dotProduct_smul]

/-- Equal-sign term at `(x₁,y₂,x₃,y₄)`: `(x₁*y₄)(x₃*y₂) = c₀² P𝕊⊗P𝕊`. -/
theorem same_main_one (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    crossedTensor (nearSel W *ᵥ v₁) (wardF b E XX *ᵥ v₂) (nearSel W *ᵥ v₃) (wardF b E XX *ᵥ v₄)
        1 1 = cZero b E ^ 2 * crossedTensor v₁ v₂ v₃ v₄ (nearProjection W * twoPortScattering b E XX)
          (nearProjection W * twoPortScattering b E XX) := by
  rw [crossedTensor, crossedTensor, bilinear_mulVec_one, bilinear_mulVec_one, iota_wardF b E hη,
    bilinear_smul', bilinear_smul']
  ring

/-- Equal-sign term at `(x₂,y₁,x₄,y₃)`, conjugated: `conj((x₂*y₃)(x₄*y₁)) = c₀² 𝕊*P⊗𝕊*P`. -/
theorem same_main_two (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    star (crossedTensor (nearSel W *ᵥ v₂) (wardF b E XX *ᵥ v₁) (nearSel W *ᵥ v₄)
        (wardF b E XX *ᵥ v₃) 1 1) = cZero b E ^ 2 * crossedTensor v₁ v₂ v₃ v₄
          ((twoPortScattering b E XX)ᴴ * nearProjection W)
          ((twoPortScattering b E XX)ᴴ * nearProjection W) := by
  rw [crossedTensor, crossedTensor, bilinear_mulVec_one, bilinear_mulVec_one, star_mul',
    ← bilinear_conjTranspose, ← bilinear_conjTranspose, iota_wardF_conj b E hη, bilinear_smul',
    bilinear_smul']
  ring

/-- Opposite-sign term at `(x₁,y₂;x₄,y₃)`: `(x₁*x₄)(y₃*y₂) = (4η²)⁻¹ P⊗P'`. -/
theorem opp_main_one (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    bilinear (nearSel W *ᵥ v₁) 1 (nearSel W *ᵥ v₄) *
        bilinear (wardF b E XX *ᵥ v₃) 1 (wardF b E XX *ᵥ v₂) =
      ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ * crossedTensor v₁ v₂ v₃ v₄ (nearProjection W)
        ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) := by
  rw [crossedTensor, bilinear_mulVec_one, bilinear_mulVec_one, nearSel_conj_mul_nearSel,
    wardF_conj_mul b E hη, bilinear_smul']
  ring

/-- Opposite-sign term at `(x₃,y₄;x₂,y₁)`: `(x₃*x₂)(y₁*y₄) = (4η²)⁻¹ P'⊗P`. -/
theorem opp_main_two (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    bilinear (nearSel W *ᵥ v₃) 1 (nearSel W *ᵥ v₂) *
        bilinear (wardF b E XX *ᵥ v₁) 1 (wardF b E XX *ᵥ v₄) =
      ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ * crossedTensor v₁ v₂ v₃ v₄
        ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX)
        (nearProjection W) := by
  rw [crossedTensor, bilinear_mulVec_one, bilinear_mulVec_one, nearSel_conj_mul_nearSel,
    wardF_conj_mul b E hη, bilinear_smul']
  ring

/-- **The main covariance tensor** is the sum of the four `Δ` main terms. -/
theorem main_match (b E : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : W ≠ 0) (s : ℂ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    let P := nearProjection W
    let S := twoPortScattering b E XX
    let P' := Sᴴ * P * S
    let η2 : ℂ := ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ)
    let x := fun v : Fin 2 × Fin W → ℂ => nearSel W *ᵥ v
    let y := fun v : Fin 2 × Fin W → ℂ => wardF b E XX *ᵥ v
    (((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
          (crossedTensor v₁ v₂ v₃ v₄ P P' + crossedTensor v₁ v₂ v₃ v₄ P' P) -
        sigmaMinus b E s / η2 * crossedTensor v₁ v₂ v₃ v₄ (P * S) (P * S) -
        conj (sigmaMinus b E s) / η2 * crossedTensor v₁ v₂ v₃ v₄ (Sᴴ * P) (Sᴴ * P) =
      sigmaMinus b E s / W * crossedTensor (x v₁) (y v₂) (x v₃) (y v₄) 1 1 +
        ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear (x v₁) 1 (x v₄) * bilinear (y v₃) 1 (y v₂)) +
        ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear (x v₃) 1 (x v₂) * bilinear (y v₁) 1 (y v₄)) +
        star (sigmaMinus b E s / W * crossedTensor (x v₂) (y v₁) (x v₄) (y v₃) 1 1) := by
  intro P S P' η2 x y
  have hη := (etaZ_pos b E (by linarith) h1 h2).ne'
  have hηc : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hstar : star (sigmaMinus b E s / W * crossedTensor (x v₂) (y v₁) (x v₄) (y v₃) 1 1) =
      conj (sigmaMinus b E s) / W *
        star (crossedTensor (x v₂) (y v₁) (x v₄) (y v₃) 1 1) := by
    rw [star_mul', star_div₀, Complex.star_def, Complex.conj_natCast]
  have hσ : ((sigmaPlus b : ℝ) : ℂ) = 2 * (etaZ b E : ℂ) ^ 2 * (transportD0 b E : ℂ) := by
    rw [sigmaPlus_eq b E hb0 h1 h2]; push_cast; ring
  rw [hstar, same_main_two b E hη, same_main_one b E hη, opp_main_one b E hη,
    opp_main_two b E hη, cZero_sq b E hη, hσ]
  simp only [η2]
  push_cast
  field_simp
  ring

end BlockBand.SourceProcess.FullSourceCovariance
