module

public import BlockBand.Transmission.Bridge.Passive

/-!
# Scattering matrix, current and conductance of the two-input path

Main results (with `𝕏_j = pathSchur E (pathAt W j ω)`):

* `boundaryResolvent_eq`, `scatteringMatrix_eq`, `pathCurrent_eq`: the port block of the full
  inverse with two matched leads is `twoPortResolvent b E 𝕏_j`, hence
  `scatteringMatrix = twoPortScattering b E 𝕏_j` and `pathCurrent = 𝕊ᴴP𝕊 - P` at `𝕏_j`
  (hypothesis: `H_path - E` invertible);
* `portBlock_twoPortResolvent_zero_zero`: `[(z - 𝕏)⁻¹]₀₀ = (z - X)⁻¹ = R`, `X = nearSchur z 𝕏`;
* `twoPortScattering_unitary`: `𝕊ᴴ𝕊 = 1` for Hermitian `𝕏`, `Im z > 0`;
* `conductanceOf_eq_half_trace_sq`: `g = Tr T(X) = ½ Re Tr J²` for Hermitian `𝕏`;
* `pathConductance_eq_half_trace_sq`: the same along the unabsorbed path.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-!
## Block inverses
-/

/-- Bottom-right block of a block inverse with invertible top-left block (totalized inverses). -/
theorem toBlocks₂₂_inv_fromBlocks {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : IsUnit A) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let : Invertible A := hA.invertible
  by_cases hS : IsUnit (D - C * A⁻¹ * B)
  · have hS' : IsUnit (D - C * ⅟A * B) := by simpa only [invOf_eq_nonsing_inv] using hS
    let : Invertible (D - C * ⅟A * B) := hS'.invertible
    let : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₁₁Invertible A B C D
    rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq]
    simp only [toBlocks_fromBlocks₂₂, invOf_eq_nonsing_inv]
  · have hM : ¬ IsUnit (Matrix.fromBlocks A B C D) := by
      rw [isUnit_fromBlocks_iff_of_invertible₁₁]; simpa only [invOf_eq_nonsing_inv] using hS
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det]),
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det])]
    rfl

/-- Near/far splitting of the two-port index. -/
def portEquiv (W : ℕ) : Fin W ⊕ Fin W ≃ Fin 2 × Fin W where
  toFun
    | Sum.inl x => (0, x)
    | Sum.inr x => (1, x)
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp

theorem submatrix_portEquiv (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    M.submatrix (portEquiv W) (portEquiv W) =
      Matrix.fromBlocks (portBlock M 0 0) (portBlock M 0 1) (portBlock M 1 0) (portBlock M 1 1) := by
  ext (x | x) (y | y) <;> rfl

/-- `R = [(z - 𝕏)⁻¹]₀₀ = (z - X)⁻¹`, whenever `z - 𝕏₁₁` is invertible. -/
theorem portBlock_twoPortResolvent_zero_zero (b E : ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)) :
    portBlock (twoPortResolvent b E XX) 0 0 = passiveResolvent b E (nearSchur (boundaryZ b E) XX) := by
  have h1 : portBlock (twoPortResolvent b E XX) 0 0 =
      (((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX).submatrix
        (portEquiv W) (portEquiv W))⁻¹).toBlocks₁₁ := by
    rw [Matrix.inv_submatrix_equiv]; rfl
  have hblk : (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX).submatrix
      (portEquiv W) (portEquiv W) = Matrix.fromBlocks
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 0 0) (-portBlock XX 0 1)
        (-portBlock XX 1 0) (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) := by
    rw [submatrix_portEquiv]
    congr 1 <;> ext x y <;> simp [portBlock, Matrix.one_apply]
  rw [h1, hblk, toBlocks₁₁_inv_fromBlocks _ _ _ _ hD, passiveResolvent, nearSchur]
  congr 1
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

/-!
## The full inverse with two matched leads
-/

theorem absorptionDiag_zero (r : ℕ) : absorptionDiag W (layerAbsorption W (fun _ => 0) r) = 0 := by
  ext x y; simp [absorptionDiag, layerAbsorption]

/-- The unabsorbed `absorbedPathSchur` is the `Layers.pathSchur` (the matrix `𝕏_j`). -/
theorem absorbedPathSchur_zero (E : ℝ) (r : ℕ) (ω : GrowthPath W) :
    absorbedPathSchur E (layerAbsorption W (fun _ => 0) r) (pathAt W r ω) =
      pathSchur E (pathAt W r ω) := by
  rw [absorbedPathSchur, absorptionDiag_zero, add_zero, pathSchur]

/-- `X_j = nearSchur z 𝕏_j` for the unabsorbed path. -/
theorem pathX_eq (b E : ℝ) (r : ℕ) (ω : GrowthPath W) :
    pathX b E W r ω = nearSchur (boundaryZ b E) (pathSchur E (pathAt W r ω)) := by
  rw [pathX, pathNearSchur, absorbedPathSchur_zero]

/-- The port block `ℝ` of `G = 𝓜⁻¹` is `(z - 𝕏_j)⁻¹`. -/
theorem boundaryResolvent_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    boundaryResolvent b E W n ω = twoPortResolvent b E (pathSchur E (pathAt W n ω)) := by
  rw [boundaryResolvent, fullInverse, fullPathMatrix, toBlocks₂₂_inv_fromBlocks _ _ _ _ hF,
    twoPortResolvent, pathSchur]

/-- `scatteringMatrix b E W j = twoPortScattering b E 𝕏_j`. -/
theorem scatteringMatrix_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    scatteringMatrix b E W n ω = twoPortScattering b E (pathSchur E (pathAt W n ω)) := by
  rw [scatteringMatrix, boundaryResolvent_eq b E n ω hF, twoPortScattering]

/-- `J = 𝕊ᴴP𝕊 - P` with `𝕊 = twoPortScattering b E 𝕏_j`. -/
theorem pathCurrent_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    pathCurrent b E W n ω =
      (twoPortScattering b E (pathSchur E (pathAt W n ω)))ᴴ * nearProjection W *
        twoPortScattering b E (pathSchur E (pathAt W n ω)) - nearProjection W := by
  rw [pathCurrent, scatteringMatrix_eq b E n ω hF]

/-!
## Unitarity and the conductance
-/

theorem matrixImaginaryPart_hermitian {n : Type*} (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    matrixImaginaryPart M = 0 := by
  rw [matrixImaginaryPart, hM.eq, sub_self, smul_zero]

/-- `𝕊ᴴ𝕊 = 1 = 𝕊𝕊ᴴ` for a Hermitian two-port `𝕏` and `Im z = η > 0`. -/
theorem twoPortScattering_unitary (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : XX.IsHermitian) (hη : 0 < (boundaryZ b E).im) :
    (twoPortScattering b E XX)ᴴ * twoPortScattering b E XX = 1 ∧
      twoPortScattering b E XX * (twoPortScattering b E XX)ᴴ = 1 := by
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX) :=
    portPencil_isUnit XX hX hη
  have hbal := passive_scattering_physical (boundaryZ b E • 1 - XX) (boundaryZ b E • 1 - XX)⁻¹ 0
    (etaZ b E) (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)) (by
      have hp : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX =
          portPencil XX (boundaryZ b E) := rfl
      rw [Matrix.star_eq_conjTranspose, matrix_difference_eq_twoI_imaginaryPart, hp,
        matrixImaginaryPart_portPencil_general, matrixImaginaryPart_hermitian XX hX, etaZ]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
        smul_eq_mul, Complex.real_smul, sub_zero, smul_zero, add_zero]
      ring)
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, Matrix.star_eq_conjTranspose] at hbal
  have hc : (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = 2 * Complex.I * (etaZ b E : ℂ) := by
    push_cast; ring
  have h1 : (twoPortScattering b E XX)ᴴ * twoPortScattering b E XX = 1 := by
    rw [twoPortScattering, twoPortResolvent, hc]
    exact (sub_eq_zero.mp hbal).symm
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

theorem trace_nearProjection_mul (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (nearProjection W * Z).trace = (portBlock Z 0 0).trace := by
  simp [Matrix.trace, nearProjection, Matrix.diagonal_mul, Fintype.sum_prod_type, Fin.sum_univ_two,
    portBlock]

theorem portBlock_sandwich_nearProjection (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    portBlock (Mᴴ * nearProjection W * M) 0 0 = (portBlock M 0 0)ᴴ * portBlock M 0 0 := by
  ext x y
  simp [portBlock, Matrix.mul_apply, nearProjection, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem nearProjection_mul_self : nearProjection W * nearProjection W = nearProjection W := by
  rw [nearProjection, Matrix.diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

/-- **Conductance as a current square**: for a Hermitian two-port `𝕏` and `Im z > 0`,
`g = conductanceOf T(X) = ½ Re Tr J²`, `X = nearSchur z 𝕏`, `J = 𝕊ᴴP𝕊 - P`. -/
theorem conductanceOf_eq_half_trace_sq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : XX.IsHermitian) (hη : 0 < (boundaryZ b E).im) :
    conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) =
      ((((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX -
        nearProjection W) ^ 2).trace.re) / 2 := by
  set S := twoPortScattering b E XX
  set P := nearProjection W
  obtain ⟨hSS, hSS'⟩ := twoPortScattering_unitary b E XX hX hη
  have hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    portPencil_isUnit _ (by
      ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
        congrFun (congrFun hX (1, x)) (1, y)) hη
  have hS00 : portBlock S 0 0 = passiveS b E (nearSchur (boundaryZ b E) XX) := by
    rw [passiveS, ← portBlock_twoPortResolvent_zero_zero b E XX hD]
    ext x y; simp [S, twoPortScattering, portBlock, Matrix.one_apply]; left; ring
  have hsq : (Sᴴ * P * S - P) ^ 2 = Sᴴ * P * S - Sᴴ * P * S * P - P * (Sᴴ * P * S) + P := by
    have h1 : Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * S := by
      calc Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * (S * Sᴴ) * P * S := by simp only [Matrix.mul_assoc]
        _ = Sᴴ * P * S := by rw [hSS', Matrix.mul_one, Matrix.mul_assoc Sᴴ P P,
              nearProjection_mul_self]
    rw [sq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, nearProjection_mul_self]
    abel
  have htr1 : (Sᴴ * P * S).trace = P.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS', Matrix.one_mul]
  have htr2 : (Sᴴ * P * S * P).trace = (P * (Sᴴ * P * S)).trace := Matrix.trace_mul_comm _ _
  have htrP : P.trace = W := by
    simp only [P, nearProjection, Matrix.trace_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp
  rw [hsq, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr1, htr2,
    trace_nearProjection_mul, portBlock_sandwich_nearProjection, hS00, htrP,
    passiveTransmission_eq_one_sub, conductanceOf, Matrix.trace_sub, Matrix.trace_one,
    Fintype.card_fin]
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re]
  ring

theorem pathSchur_isHermitian (E : ℝ) (r : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian) :
    (pathSchur E (pathAt W r ω)).IsHermitian := by
  have hH : (pathMatrix (pathAt W r ω) - (E : ℂ) • 1).IsHermitian :=
    (pathMatrix_pathAt_isHermitian r ω hA).sub (by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Complex.star_def, Complex.conj_ofReal])
  rw [pathSchur]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hH.inv

/-- **Conductance along the path**: `g_j = pathConductance = ½ Re Tr J_j²`, for Hermitian
blocks, `Im z > 0` and `H_path - E` invertible. -/
theorem pathConductance_eq_half_trace_sq (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    pathConductance b E W n ω = ((pathCurrent b E W n ω) ^ 2).trace.re / 2 := by
  rw [pathConductance, pathTransmission, ← pathX, pathX_eq, pathCurrent_eq b E n ω hF]
  exact conductanceOf_eq_half_trace_sq b E _ (pathSchur_isHermitian E n ω hA) hη

end BlockBand.Transmission.Bridge
