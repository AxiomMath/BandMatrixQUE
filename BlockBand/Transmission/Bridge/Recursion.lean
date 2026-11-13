module

public import BlockBand.Transmission.Bridge.PathPencil
public import BlockBand.Transmission.SchurPassivity

/-!
# The exact near-end recursion along one sample

Main results (for every length `r ≥ 1`, along one sample `ω`):

* `pathNearSchur_eq_lead`: `X_r = C_nᴴ F̃_r⁻¹ C_n` (far lead eliminated by Woodbury);
* `pathNearSchur_succ`: `X_{r+1} = B_{r+1}ᴴ (A_r - E + iε₀ - X_r)⁻¹ B_{r+1}`,
  `ε₀ = κ((r+1)/W)/W²`;
* `pathNearSchur_succ_eq_freshSchur`: the same as `freshSchur E (X_r - iε₀) (freshSample W r ω)`;
  for `κ = 0`, `pathX (r+1) = freshSchur E (pathX r) (freshSample W r ω)`.

Hypotheses: invertibility of the path pencils `F_r`, `F_{r+1}` (`H_path - E + i diag ε`), and of
`z - 𝕏₁₁` at both lengths; the latter follow from Hermitian blocks, `κ ≥ 0` and `Im z > 0`
(`isUnit_farPencil`). The case `r = 0` is excluded: `X_0 = 0`, while
`X_1 = B_1ᴴ(A_0 - E + iε - B_0 z⁻¹ B_0ᴴ)⁻¹ B_1` (the far lead sits on the first block).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix ComplexOrder

/-!
## Two generic block identities
-/

/-- Top-left block of a block inverse with invertible bottom-right block (totalized inverses). -/
theorem toBlocks₁₁_inv_fromBlocks {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁ = (A - B * D⁻¹ * C)⁻¹ := by
  let : Invertible D := hD.invertible
  by_cases hS : IsUnit (A - B * D⁻¹ * C)
  · have hS' : IsUnit (A - B * ⅟D * C) := by simpa only [invOf_eq_nonsing_inv] using hS
    let : Invertible (A - B * ⅟D * C) := hS'.invertible
    let : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₂₂Invertible A B C D
    rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq]
    simp only [toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv]
  · have hM : ¬ IsUnit (Matrix.fromBlocks A B C D) := by
      rw [isUnit_fromBlocks_iff_of_invertible₂₂]; simpa only [invOf_eq_nonsing_inv] using hS
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det]),
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det])]
    rfl

/-- Woodbury form of the elimination of a matched lead `z`. -/
theorem lead_woodbury {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (F : Matrix n n ℂ) (Cf : Matrix n k ℂ) {z : ℂ} (hz : z ≠ 0) (hF : IsUnit F)
    (hK : IsUnit (z • (1 : Matrix k k ℂ) - Cfᴴ * F⁻¹ * Cf)) :
    (F - z⁻¹ • (Cf * Cfᴴ))⁻¹ =
        F⁻¹ + F⁻¹ * Cf * (z • (1 : Matrix k k ℂ) - Cfᴴ * F⁻¹ * Cf)⁻¹ * Cfᴴ * F⁻¹ ∧
      IsUnit (F - z⁻¹ • (Cf * Cfᴴ)) := by
  set C : Matrix k k ℂ := (-z⁻¹) • 1
  have hCinv : C⁻¹ = (-z) • 1 := by
    apply Matrix.inv_eq_right_inv
    simp only [C, smul_mul_smul_comm, Matrix.one_mul]
    rw [neg_mul_neg, inv_mul_cancel₀ hz, one_smul]
  have hC : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [C, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero hz))).pow _
  have hsum : C⁻¹ + Cfᴴ * F⁻¹ * Cf = -(z • (1 : Matrix k k ℂ) - Cfᴴ * F⁻¹ * Cf) := by
    rw [hCinv]; simp only [neg_sub, neg_smul]; abel
  have hAC : IsUnit (C⁻¹ + Cfᴴ * F⁻¹ * Cf) := by rw [hsum]; exact hK.neg
  have hF' : F - z⁻¹ • (Cf * Cfᴴ) = F + Cf * C * Cfᴴ := by
    simp only [C, sub_eq_add_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, neg_smul]
  have hnegInv : (-(z • (1 : Matrix k k ℂ) - Cfᴴ * F⁻¹ * Cf))⁻¹ =
      -(z • (1 : Matrix k k ℂ) - Cfᴴ * F⁻¹ * Cf)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [neg_mul_neg, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)]
  refine ⟨?_, ?_⟩
  · rw [hF', Matrix.add_mul_mul_inv_eq_sub F Cf C Cfᴴ hF hC hAC, hsum, hnegInv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  · rw [hF']
    let : Invertible F := hF.invertible
    let : Invertible C := hC.invertible
    have hAC' : IsUnit (⅟C + Cfᴴ * ⅟F * Cf) := by
      simpa only [invOf_eq_nonsing_inv] using hAC
    let : Invertible (⅟C + Cfᴴ * ⅟F * Cf) := hAC'.invertible
    let := Matrix.invertibleAddMulMul F Cf C Cfᴴ
    exact isUnit_of_invertible _

/-- `(fromRows B 0)ᴴ M (fromRows B 0) = Bᴴ M₁₁ B`. -/
theorem fromRows_zero_sandwich {m n k : Type*} [Fintype m] [Fintype n]
    (B : Matrix m k ℂ) (M : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    (((Matrix.fromRows B (0 : Matrix n k ℂ))ᴴ * M : Matrix k (m ⊕ n) ℂ) *
        (Matrix.fromRows B (0 : Matrix n k ℂ) : Matrix (m ⊕ n) k ℂ) : Matrix k k ℂ) =
      Bᴴ * M.toBlocks₁₁ * B := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero, Matrix.mul_zero]

/-!
## The near Schur matrix through the lead-closed pencil
-/

variable {W : ℕ}

/-- `z - 𝕏₁₁ = z - C_fᴴ F⁻¹ C_f`, the far pencil of the length-`r` path. -/
def farPencil (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  boundaryZ b E • 1 - (farCol W r ω)ᴴ * (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))⁻¹ *
    farCol W r ω

/-- **Far port eliminated by its lead**: `X_r = C_nᴴ F̃_r⁻¹ C_n`, and `F̃_r` is
invertible, whenever `F_r` and `z - 𝕏₁₁` are invertible. -/
theorem pathNearSchur_eq_lead (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) (ω : GrowthPath W)
    (hz : boundaryZ b E ≠ 0) (hF : IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω)))
    (hK : IsUnit (farPencil b E κ W r ω)) :
    pathNearSchur b E κ W r ω = (nearCol W r ω)ᴴ * (leadPencil b E κ W r ω)⁻¹ * nearCol W r ω ∧
      IsUnit (leadPencil b E κ W r ω) := by
  obtain ⟨hW, hU⟩ := lead_woodbury _ (farCol W r ω) hz hF hK
  refine ⟨?_, hU⟩
  rw [leadPencil, hW]
  simp only [pathNearSchur, nearSchur, portBlock_absorbedPathSchur]
  change (nearCol W r ω)ᴴ * _ * nearCol W r ω + (nearCol W r ω)ᴴ * _ * farCol W r ω *
    (farPencil b E κ W r ω)⁻¹ * ((farCol W r ω)ᴴ * _ * nearCol W r ω) = _
  simp only [farPencil, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- **Exact near-end recursion**: for `r ≥ 1`, along one sample,
`X_{r+1} = B_{r+1}ᴴ (A_r - E + iε₀ - X_r)⁻¹ B_{r+1}`, `ε₀ = κ((r+1)/W)/W²`,
given invertible path pencils and far pencils at lengths `r` and `r+1`. -/
theorem pathNearSchur_succ (b E : ℝ) (κ : ℝ → ℝ) {r : ℕ} (hr : 1 ≤ r) (ω : GrowthPath W)
    (hz : boundaryZ b E ≠ 0)
    (hF : IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω)))
    (hK : IsUnit (farPencil b E κ W r ω))
    (hF' : IsUnit (pathPencil E (layerAbsorption W κ (r + 1)) (pathAt W (r + 1) ω)))
    (hK' : IsUnit (farPencil b E κ W (r + 1) ω)) :
    pathNearSchur b E κ W (r + 1) ω =
      (ω.2 (r + 1))ᴴ * (ω.1 r - (E : ℂ) • 1 +
        (((layerAbsorption W κ (r + 1) 0 : ℝ) : ℂ) * Complex.I) • 1 -
          pathNearSchur b E κ W r ω)⁻¹ * ω.2 (r + 1) := by
  obtain ⟨h0, hU0⟩ := pathNearSchur_eq_lead b E κ r ω hz hF hK
  obtain ⟨h1, -⟩ := pathNearSchur_eq_lead b E κ (r + 1) ω hz hF' hK'
  set e := headEquiv r W
  have hre : ∀ G : Matrix (Fin (r + 1) × Fin W) (Fin (r + 1) × Fin W) ℂ,
      (nearCol W (r + 1) ω)ᴴ * G * nearCol W (r + 1) ω =
        ((nearCol W (r + 1) ω).submatrix e id)ᴴ * G.submatrix e e *
          (nearCol W (r + 1) ω).submatrix e id := by
    intro G
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  rw [h1, hre, ← Matrix.inv_submatrix_equiv, leadPencil_succ_submatrix b E κ hr ω,
    nearCol_succ_submatrix]
  refine (fromRows_zero_sandwich _ _).trans ?_
  rw [toBlocks₁₁_inv_fromBlocks _ _ _ _ hU0, h0]

/-- The one-block fresh Schur matrix in `Fin W` coordinates:
`freshSchur E X (A, B) = Bᴴ (A - E - X)⁻¹ B`. -/
theorem freshSchur_eq (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) :
    freshSchur E X ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort) =
      Bᴴ * (A - (E : ℂ) • 1 - X)⁻¹ * B := by
  let e : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm
  have hM : (BlockBand.Internal.Contracts.Layers.blockDiag (fun _ : Fin 1 => A) - (E : ℂ) • 1 -
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)).submatrix e e =
        A - (E : ℂ) • 1 - X := by
    ext x y; simp [e, BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.one_apply]
  have hB : (bondMatrix LayerShape.oneBlockOnePort (fun _ _ => B)).submatrix e e = B := by
    ext x y; simp [e, bondMatrix, LayerShape.incident]
  have : freshSchur E X ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort) =
      (layerSchur .oneBlockOnePort E (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)
        (fun _ => A, fun _ _ => B)).submatrix e e := by
    ext x y; simp [freshSchur, e]
  rw [this, layerSchur, ← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e,
    ← Matrix.conjTranspose_submatrix, ← Matrix.inv_submatrix_equiv, hM, hB]

/-- **The near-end recursion in `freshSchur` form**: for `r ≥ 1`, `X_{r+1}` is the one-layer
Schur matrix `freshSchur E (X_r - iε₀) (freshSample W r ω)` of the fresh layer at the old input
`X_r - iε₀` (absorption of the fresh block moved into the input). -/
theorem pathNearSchur_succ_eq_freshSchur (b E : ℝ) (κ : ℝ → ℝ) {r : ℕ} (hr : 1 ≤ r)
    (ω : GrowthPath W) (hz : boundaryZ b E ≠ 0)
    (hF : IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω)))
    (hK : IsUnit (farPencil b E κ W r ω))
    (hF' : IsUnit (pathPencil E (layerAbsorption W κ (r + 1)) (pathAt W (r + 1) ω)))
    (hK' : IsUnit (farPencil b E κ W (r + 1) ω)) :
    pathNearSchur b E κ W (r + 1) ω =
      freshSchur E (pathNearSchur b E κ W r ω -
        (((layerAbsorption W κ (r + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) (freshSample W r ω) := by
  rw [pathNearSchur_succ b E κ hr ω hz hF hK hF' hK', freshSample, freshSchur_eq]
  congr 2
  rw [sub_sub_eq_add_sub, sub_add_eq_add_sub]

/-- Homogeneous case (`κ = 0`): `pathX (r+1) = freshSchur E (pathX r) (freshSample W r ω)`. -/
theorem pathX_succ (b E : ℝ) {r : ℕ} (hr : 1 ≤ r) (ω : GrowthPath W) (hz : boundaryZ b E ≠ 0)
    (hF : IsUnit (pathPencil E (layerAbsorption W (fun _ => 0) r) (pathAt W r ω)))
    (hK : IsUnit (farPencil b E (fun _ => 0) W r ω))
    (hF' : IsUnit (pathPencil E (layerAbsorption W (fun _ => 0) (r + 1)) (pathAt W (r + 1) ω)))
    (hK' : IsUnit (farPencil b E (fun _ => 0) W (r + 1) ω)) :
    pathX b E W (r + 1) ω = freshSchur E (pathX b E W r ω) (freshSample W r ω) := by
  have := pathNearSchur_succ_eq_freshSchur b E (fun _ => 0) hr ω hz hF hK hF' hK'
  simpa [layerAbsorption] using this

end BlockBand.Transmission.Bridge
