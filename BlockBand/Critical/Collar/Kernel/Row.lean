module

public import BlockBand.Critical.Collar.Kernel.Collar
public import BlockBand.Critical.Collar.Density.Statement

/-!
# The boundary kernel through the full three-block resolvent (fresh-row identity)

Support for the collar kernel theorem. The boundary kernel is obtained by moving the terminating
factors through the top spectral projector before eliminating the fresh middle block; that order
is why the unbounded Schur load `B(G - e)⁻¹B*` creates no unmatched weight. At a zero eigenvector
`(v,w)`, `K_X v = (z_b + e - A)v - Bw`.

*Setting.* One collar sample `ω` with Hermitian `A_j, G`, real shift `s`, zero height,
`D = G - (e+s)` invertible (true `collarLaw`-a.s.), `X = X_h - iY` with `Y = -Im X ≻ 0`. Let
`𝓗 = ℋ_X` at energy `e + s` (`collarMatrix (e+s) X ω`), `𝓡 = 𝓗⁻¹`, `Ŷ = diag(Y, 0)`, and the fresh
row `ρ = (z_b + e + s - A, -B)` (`collarRow`).

## Results

* `isUnit_det_collarMatrix`: `𝓗` is invertible.
* `collarResolvent_mul_top`: `𝓡 E₁ = (R_c ; -D⁻¹B*R_c)`, `R_c = collarSchur⁻¹ = (𝓡)₁₁`.
* `one_sub_mul_collarSchur_inv`: `I - (z_b - X)R_c = -ρ c`, `c = (R_c ; -D⁻¹B*R_c) = 𝓡E₁`
  (the fresh-row identity).
* `collar_poissonKernel_eq_row`: `𝒫(Ur) = η⁻¹ (ρc) Y (ρc)*`.
* `collarMatrix_sub_conjTranspose`, `collarResolvent_ward`: `𝓗 - 𝓗* = 2iŶ` and
  `𝓡 Ŷ 𝓡* = (2i)⁻¹(𝓡* - 𝓡)`, `Ŷ = diag(Y, 0)`.
The identity `c Y c* = 𝓡Ŷ𝓡*` and its consequence `q*𝒫(Ur)q = -η⁻¹ Im⟨ρ*q, 𝓡ρ*q⟩` are proved in
the sibling module as `collarResolvent_top_sandwich` and `collar_poissonKernel_quad`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density (collarMatrix)
open scoped ComplexOrder

variable {W : ℕ}

/-- The fresh row `ρ = (z_b + e + s - A, -B)` (`2W × 3W`). -/
def collarRow (b e s : ℝ) (ω : Critical.CollarSample W) :
    Matrix (Fin 2 × Fin W) (LayerSite W .common) ℂ :=
  Matrix.fromCols ((boundaryZ b e + ((e + s : ℝ) : ℂ)) • 1 - Layers.blockDiag ω.1.1)
    (-bondMatrix .common ω.1.2)

/-- `E₁ = (I ; 0)`: the inclusion of the old ports into `LayerSite W .common` (`collarResolvent_mul_top`
computes `𝓡E₁`). -/
def topInclusion : Matrix (LayerSite W .common) (Fin 2 × Fin W) ℂ := Matrix.fromRows 1 0

/-- `Ŷ = diag(Y, 0)`. -/
def topLift (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (LayerSite W .common) (LayerSite W .common) ℂ := Matrix.fromBlocks Y 0 0 0

/-- The middle block `D = G - (e+s)`. -/
abbrev middleBlock (e s : ℝ) (ω : Critical.CollarSample W) :
    Matrix (PortSite W .common) (PortSite W .common) ℂ := ω.2 - ((e + s : ℝ) : ℂ) • 1

theorem collarMatrix_eq_fromBlocks (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    collarMatrix (e + s) X ω = Matrix.fromBlocks (Layers.blockDiag ω.1.1 - ((e + s : ℝ) : ℂ) • 1 - X)
      (bondMatrix .common ω.1.2) (bondMatrix .common ω.1.2)ᴴ (middleBlock e s ω) := rfl

/-- `𝓗 = ℋ_X` (energy `e+s`) is invertible when `D` is invertible and `Y = -Im X ≻ 0`
(Hermitian `A_j`, `G`): `det 𝓗 = det D · det(collarSchur)`. -/
theorem isUnit_det_collarMatrix (b e s : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (hD : IsUnit (middleBlock e s ω).det) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosDef) : IsUnit (collarMatrix (e + s) X ω).det := by
  have hS : IsUnit (collarSchur e s X ω).det := by
    rw [← collarReaction_add b e s X ω]
    refine isUnit_det_herm_add_I_smul_posDef ((collarReaction_isHermitian b e s hA hG).add ?_) hY
    exact (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  let _ : Invertible (middleBlock e s ω) := (middleBlock e s ω).invertibleOfIsUnitDet hD
  rw [collarMatrix_eq_fromBlocks, Matrix.det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  exact hD.mul hS

/-- `𝓗 · (R_c ; -D⁻¹B*R_c) = E₁` (given `D`, `collarSchur` invertible). -/
theorem collarMatrix_mul_column (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) (hD : IsUnit (middleBlock e s ω).det)
    (hS : IsUnit (collarSchur e s X ω).det) :
    collarMatrix (e + s) X ω * Matrix.fromRows (collarSchur e s X ω)⁻¹
        (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹)) =
      topInclusion := by
  set S := collarSchur e s X ω
  set D := middleBlock e s ω
  set B := bondMatrix .common ω.1.2
  rw [collarMatrix_eq_fromBlocks, fromBlocks_mul_fromRows, topInclusion]
  congr 1
  · have : Layers.blockDiag ω.1.1 - ((e + s : ℝ) : ℂ) • 1 - X = S + B * D⁻¹ * Bᴴ := by
      simp only [S, collarSchur, D, B, middleBlock]; abel
    have e1 : S * S⁻¹ = 1 := mul_nonsing_inv _ hS
    rw [this]
    simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.mul_assoc, e1]
    abel
  · rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hD,
      Matrix.one_mul, add_neg_cancel]

/-- `𝓡 E₁ = (R_c ; -D⁻¹B*R_c)`. -/
theorem collarResolvent_mul_top (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) (hD : IsUnit (middleBlock e s ω).det)
    (hS : IsUnit (collarSchur e s X ω).det) (hH : IsUnit (collarMatrix (e + s) X ω).det) :
    (collarMatrix (e + s) X ω)⁻¹ * topInclusion =
      Matrix.fromRows (collarSchur e s X ω)⁻¹
        (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹)) := by
  set col := Matrix.fromRows (collarSchur e s X ω)⁻¹
    (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹))
  calc (collarMatrix (e + s) X ω)⁻¹ * topInclusion
      = (collarMatrix (e + s) X ω)⁻¹ * (collarMatrix (e + s) X ω * col) :=
        congrArg (fun M => (collarMatrix (e + s) X ω)⁻¹ * M)
          (collarMatrix_mul_column e s X ω hD hS).symm
    _ = ((collarMatrix (e + s) X ω)⁻¹ * collarMatrix (e + s) X ω) * col :=
        (Matrix.mul_assoc _ _ _).symm
    _ = col := by rw [nonsing_inv_mul _ hH, Matrix.one_mul]

/-- **Fresh-row identity**: `I - (z_b - X)R_c = -ρ (R_c ; -D⁻¹B*R_c)` (only `collarSchur`
invertible is needed). -/
theorem one_sub_mul_collarSchur_inv (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) (hS : IsUnit (collarSchur e s X ω).det) :
    1 - (boundaryZ b e • 1 - X) * (collarSchur e s X ω)⁻¹ =
      -(collarRow b e s ω * Matrix.fromRows (collarSchur e s X ω)⁻¹
        (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹))) := by
  set S := collarSchur e s X ω
  set D := middleBlock e s ω
  set B := bondMatrix .common ω.1.2
  rw [collarRow, fromCols_mul_fromRows]
  have hZS : boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X - S =
      (boundaryZ b e + ((e + s : ℝ) : ℂ)) • 1 - Layers.blockDiag ω.1.1 + B * D⁻¹ * Bᴴ := by
    simp only [S, collarSchur, D, B, middleBlock, add_smul]
    abel
  have e1 : S * S⁻¹ = 1 := mul_nonsing_inv _ hS
  have : (boundaryZ b e + ((e + s : ℝ) : ℂ)) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      Layers.blockDiag ω.1.1 = boundaryZ b e • 1 - X - S - B * D⁻¹ * Bᴴ := by
    rw [hZS]; abel
  rw [this]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.sub_mul, e1]
  simp only [Matrix.mul_assoc]
  abel

/-- **`𝒫(Ur)` through the fresh row and the top column of the three-block resolvent**: for one
collar sample (Hermitian `A_j`, `G`), real shift `s`, zero height and `Y = -Im X ≻ 0`, with
`c = (R_c ; -D⁻¹B*R_c) = 𝓡E₁` (`collarResolvent_mul_top`):
`𝒫(Ur) = η⁻¹ (ρc) Y (ρc)*` (for `collarScattering b e s 0` and `oldScattering`).
The Schur load `B D⁻¹ B*` enters only through `c`; no unmatched weight appears. -/
theorem collar_poissonKernel_eq_row (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : Critical.CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosDef) :
    Critical.poissonKernel (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) •
        ((collarRow b e s ω * Matrix.fromRows (collarSchur e s X ω)⁻¹
            (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹))) *
          (-Critical.imPart X) *
          (collarRow b e s ω * Matrix.fromRows (collarSchur e s X ω)⁻¹
            (-((middleBlock e s ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ * (collarSchur e s X ω)⁻¹)))ᴴ) := by
  have hS : IsUnit (collarSchur e s X ω).det := by
    rw [← collarReaction_add b e s X ω]
    refine isUnit_det_herm_add_I_smul_posDef ((collarReaction_isHermitian b e s hA hG).add ?_) hY
    exact (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  rw [(collar_poissonKernel_eq b e s hη hA hG X hY).2.1, one_sub_mul_collarSchur_inv b e s X ω hS]
  simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- `𝓗 - 𝓗* = 2i Ŷ` (Hermitian `A_j`, `G`). -/
theorem collarMatrix_sub_conjTranspose (e : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    collarMatrix e X ω - (collarMatrix e X ω)ᴴ = (2 * Complex.I) • topLift (-Critical.imPart X) := by
  have hDg := blockDiag_isHermitian' hA
  rw [collarMatrix, fromBlocks_conjTranspose, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    topLift, fromBlocks_smul]
  congr 1
  · simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hDg.eq,
      Complex.star_def, Complex.conj_ofReal, Critical.imPart, smul_neg, smul_smul]
    rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_smul]
    abel
  · simp
  · simp
  · simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hG.eq,
      Complex.star_def, Complex.conj_ofReal, smul_zero]
    abel

/-- **Ward identity for the three-block resolvent**: `𝓡 Ŷ 𝓡* = (2i)⁻¹(𝓡* - 𝓡)`. -/
theorem collarResolvent_ward (e : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hH : IsUnit (collarMatrix e X ω).det) :
    (collarMatrix e X ω)⁻¹ * topLift (-Critical.imPart X) * ((collarMatrix e X ω)⁻¹)ᴴ =
      (2 * Complex.I)⁻¹ • (((collarMatrix e X ω)⁻¹)ᴴ - (collarMatrix e X ω)⁻¹) := by
  set P := collarMatrix e X ω
  have hw : (P⁻¹)ᴴ - P⁻¹ = P⁻¹ * (P - Pᴴ) * (P⁻¹)ᴴ := by
    have h1 : P⁻¹ * P = 1 := P.nonsing_inv_mul hH
    have h2 : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [hw, collarMatrix_sub_conjTranspose e hA hG X, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_smul]

end BlockBand.Critical.Collar.Kernel
