module

public import BlockBand.SourceProcess.FullSource.RightLetter
public import BlockBand.SourceProcess.FullSource.WardAlgebra

/-!
# The inputs of the full Ward identity

The resolvent identities from which the full Ward identity is assembled.

* `pencil_sub_conj`: `K - K* = 2i(η + Y)`, `K = z - X`, `Y = -Im X`;
* `far_absorption`: `RYR* = η ℝ₁₂ℝ₁₂*` ("`-Im X = ηKℝ₁₂ℝ₁₂*K*`"), `R = K⁻¹`;
* `im_g11`: on `{A Hermitian, B invertible}`, `𝒢₁₁ - 𝒢₁₁* = -2i(𝒢₁₁Y𝒢₁₁* + η𝒢₁₂𝒢₁₂*)`;
* `ward_near`: `LL* + (Δℝ₁₂)(Δℝ₁₂)* - I = Δf + f*Δ*`, `f = R - (2iη)⁻¹` (`passiveF`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem portBlock_mul (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (M * N) i j = portBlock M i 0 * portBlock N 0 j + portBlock M i 1 * portBlock N 1 j := by
  ext x y; simp [portBlock, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem portBlock_ext {M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h : ∀ i j, portBlock M i j = portBlock N i j) : M = N := by
  ext ⟨i, x⟩ ⟨j, y⟩; exact congrFun (congrFun (h i j) x) y

theorem inv_sub_conj {n : Type*} [Fintype n] [DecidableEq n] (R K : Matrix n n ℂ)
    (hRK : R * K = 1) : R - Rᴴ = R * (Kᴴ - K) * Rᴴ := by
  have e1 : R * Kᴴ * Rᴴ = R := by
    rw [Matrix.mul_assoc, ← conjTranspose_mul, hRK, conjTranspose_one, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, e1, hRK, Matrix.one_mul]

/-- `K - K* = 2i(η + Y)` for `K = z - X`, `Y = -Im X`. -/
theorem pencil_sub_conj (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (z • 1 - X) - (z • 1 - X)ᴴ = (2 * Complex.I) • ((z.im : ℂ) • 1 + passiveY X) := by
  have hX := BlockBand.Transmission.matrix_difference_eq_twoI_imaginaryPart X
  have hz : z - star z = 2 * Complex.I * (z.im : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]; push_cast; ring
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, passiveY, smul_add, smul_smul,
    ← hz]
  rw [show (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) - (star z • 1 - Xᴴ) =
    (z - star z) • 1 - (X - Xᴴ) by rw [sub_smul]; abel, hX]
  module

/-- **Far absorption**: `R(-Im X)R* = η ℝ₁₂ℝ₁₂*`, Hermitian `𝕏`, `η > 0`. -/
theorem far_absorption (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) :
    passiveResolvent b E (nearSchur (boundaryZ b E) XX) *
        passiveY (nearSchur (boundaryZ b E) XX) *
        (passiveResolvent b E (nearSchur (boundaryZ b E) XX))ᴴ =
      ((etaZ b E : ℝ) : ℂ) • (portBlock (twoPortResolvent b E XX) 0 1 *
        (portBlock (twoPortResolvent b E XX) 0 1)ᴴ) := by
  set z := boundaryZ b E
  set X := nearSchur z XX
  set R := passiveResolvent b E X
  set Q := portBlock (twoPortResolvent b E XX) 0 1
  set Y := passiveY X
  have hz : 0 < z.im := hη
  -- the two-port resolvent
  set 𝕂 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := z • 1 - XX
  have h𝕂 : IsUnit 𝕂.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (BlockBand.Transmission.portPencil_isUnit XX hXX hz)
  have hRR : twoPortResolvent b E XX - (twoPortResolvent b E XX)ᴴ =
      (star z - z) • (twoPortResolvent b E XX * (twoPortResolvent b E XX)ᴴ) := by
    rw [show twoPortResolvent b E XX = 𝕂⁻¹ from rfl, inv_sub_conj _ 𝕂 (Matrix.nonsing_inv_mul _ h𝕂)]
    rw [show 𝕂ᴴ - 𝕂 = (star z - z) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) by
      simp only [𝕂, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hXX.eq, sub_smul]
      abel]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hD : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _ (portBlock_isHermitian hXX 1) hz
  have h00 : portBlock (twoPortResolvent b E XX) 0 0 = R :=
    portBlock_twoPortResolvent_zero_zero b E XX hD
  have hblk := congrArg (fun M => portBlock M 0 0) hRR
  have hsub : ∀ M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      portBlock (M - N) 0 0 = portBlock M 0 0 - portBlock N 0 0 := fun _ _ => rfl
  have hsmul : ∀ (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      portBlock (c • M) 0 0 = c • portBlock M 0 0 := fun _ _ => rfl
  rw [hsub, hsmul, portBlock_mul, ← portBlock_conjTranspose, ← portBlock_conjTranspose,
    h00] at hblk
  -- the one-port resolvent
  have hY : Y.PosSemidef := nearSchur_passive hz hXX
  have hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hKd := (Matrix.isUnit_iff_isUnit_det _).mp hK
  have hR1 := inv_sub_conj R (z • 1 - X) (Matrix.nonsing_inv_mul _ hKd)
  rw [show (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X)ᴴ - (z • 1 - X) =
    -((z • 1 - X) - (z • 1 - X)ᴴ) by abel, pencil_sub_conj] at hR1
  have hsz : star z - z = -(2 * Complex.I * (z.im : ℂ)) := by
    rw [Complex.star_def, ← neg_sub, Complex.sub_conj]; push_cast; ring
  rw [hblk, hsz] at hR1
  have h2I : (2 * Complex.I)⁻¹ * (2 * Complex.I) = 1 :=
    inv_mul_cancel₀ (by simp)
  simp only [Matrix.mul_neg, Matrix.neg_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one] at hR1
  show R * Y * Rᴴ = ((z.im : ℝ) : ℂ) • (Q * Qᴴ)
  linear_combination (norm := module) (2 * Complex.I)⁻¹ • hR1 -
    h2I • (R * Y * Rᴴ - ((z.im : ℝ) : ℂ) • (Q * Qᴴ))

theorem submatrix_one_embed0 :
    (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ).submatrix embed0 embed0 = 1 := by
  ext x y; simp [embed0, Matrix.one_apply]

/-- **`Im 𝒢₁₁`** on `{A Hermitian, B invertible}`:
`𝒢₁₁ - 𝒢₁₁* = -2i(𝒢₁₁Y𝒢₁₁* + η𝒢₁₂𝒢₁₂*)`, `η = Im w`, `Y = -Im X`. -/
theorem im_g11 (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    g11 E w X ω - (g11 E w X ω)ᴴ = -((2 * Complex.I) • (g11 E w X ω * passiveY X *
      (g11 E w X ω)ᴴ + (w.im : ℂ) • (g12 E w X ω * (g12 E w X ω)ᴴ))) := by
  have hS := isUnit_schurS E hw hY hA hB
  have h : layerAt E w X ω = schurInv E w X ω := (layer_schur E hw hY hA hB).2.1
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  have hbL : bondL ω = liftX (ω.2 0 0) := by rw [bondL, bondMatrix_one_eq]
  have hsum : ∀ P P' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ,
      P.submatrix embed0 embed0 + P'.submatrix embed0 embed0 = (P + P').submatrix embed0 embed0 :=
    fun _ _ => rfl
  have hJ2 : g11 E w X ω * ω.2 0 0 = -(w • g12 E w X ω) := by
    rw [g11_eq h, g12_eq h, submatrix_embed0_mul, ← hbL]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  have hJ1 : g11 E w X ω * (ω.1 0 - (E : ℂ) • 1 - X) + g12 E w X ω * (ω.2 0 0)ᴴ = 1 := by
    rw [g11_eq h, g12_eq h, submatrix_embed0_mul, submatrix_embed0_mul, hsum,
      liftX_conjTranspose, ← hbL]
    have hM : liftX (ω.1 0 - (E : ℂ) • 1 - X) - w⁻¹ • (bondL ω * (bondL ω)ᴴ) = schurS E w X ω := by
      rw [schurS, blockDiag_one_eq, liftX_sub, liftX_sub, liftX_smul, liftX_one]
    rw [show (schurS E w X ω)⁻¹ * liftX (ω.1 0 - (E : ℂ) • 1 - X) +
        -w⁻¹ • ((schurS E w X ω)⁻¹ * bondL ω) * (bondL ω)ᴴ =
        (schurS E w X ω)⁻¹ * (liftX (ω.1 0 - (E : ℂ) • 1 - X) -
          w⁻¹ • (bondL ω * (bondL ω)ᴴ)) by
      rw [Matrix.mul_sub, mul_smul_comm, smul_mul_assoc, Matrix.mul_assoc]; module,
      hM, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS), submatrix_one_embed0]
  have hblk := im_inv_block _ _ _ _ w hJ1 hJ2
  have hMM : (ω.1 0 - (E : ℂ) • 1 - X)ᴴ - (ω.1 0 - (E : ℂ) • 1 - X) =
      -((2 * Complex.I) • passiveY X) := by
    have hX := BlockBand.Transmission.matrix_difference_eq_twoI_imaginaryPart X
    rw [conjTranspose_sub, conjTranspose_sub, hA.eq, conjTranspose_smul, conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal, passiveY, smul_neg, neg_neg, ← hX]
    abel
  have hz : w - star w = 2 * Complex.I * (w.im : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]; push_cast; ring
  rw [hblk, hMM, hz]
  simp only [Matrix.mul_neg, Matrix.neg_mul, mul_smul_comm, smul_mul_assoc]
  module

/-- **The near block of the Ward identity**: `LL* + (Δℝ₁₂)(Δℝ₁₂)* - I = Δf + f*Δ*`, Hermitian `𝕏`,
on `{A Hermitian, B invertible}`. -/
theorem ward_near (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    freshL b E (nearSchur (boundaryZ b E) XX) ω * (freshL b E (nearSchur (boundaryZ b E) XX) ω)ᴴ +
        freshDelta b E (nearSchur (boundaryZ b E) XX) ω * portBlock (twoPortResolvent b E XX) 0 1 *
          (freshDelta b E (nearSchur (boundaryZ b E) XX) ω *
            portBlock (twoPortResolvent b E XX) 0 1)ᴴ - 1 =
      freshDelta b E (nearSchur (boundaryZ b E) XX) ω * passiveF b E (nearSchur (boundaryZ b E) XX) +
        (passiveF b E (nearSchur (boundaryZ b E) XX))ᴴ *
          (freshDelta b E (nearSchur (boundaryZ b E) XX) ω)ᴴ := by
  set z := boundaryZ b E
  set X := nearSchur z XX
  have hz : 0 < z.im := hη
  have hY : (passiveY X).PosSemidef := nearSchur_passive hz hXX
  have hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  rw [freshL_eq_lAt, freshDelta_eq]
  exact ward_algebra (g11 E z X ω) (g12 E z X ω) (z • 1 - X) (passiveY X)
    (passiveResolvent b E X) (portBlock (twoPortResolvent b E XX) 0 1) hη.ne'
    (im_g11 E hz hY hA hB) (pencil_sub_conj z X)
    (Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK)) (far_absorption b E hXX hη)

end BlockBand.SourceProcess.FullSource
