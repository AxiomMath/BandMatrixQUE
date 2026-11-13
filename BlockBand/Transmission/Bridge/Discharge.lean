module

public import BlockBand.Transmission.Bridge.Current

/-!
# Discharging the invertibility hypotheses of the bridges

* (a) `isUnit_pathPencil_of_pos`: if `κ > 0` at the times of the blocks of the length-`r` path,
  the path pencil `H - E + i diag ε` is invertible for **every** sample with Hermitian blocks
  (`Im = diag ε ≻ 0`). These are the hypotheses `hF`, `hF'` of `pathNearSchur_succ`.
* (b) `isUnit_freshPencil`, `isUnit_layerMatrix_fresh`, `isUnit_freshLayer_path`: the fresh layer
  matrix is invertible whenever the fresh bond `B` is invertible (`Im(A - E - X - z⁻¹BBᴴ) =
  Y + η|z|⁻²BBᴴ ≻ 0`); this is the hypothesis `hG` of `boundaryToInterior_succ`.
* (c) `isUnit_nearPencil_absorbed`: `z - X_r` is invertible for every `κ ≥ 0`.

Not proved here: the almost-sure invertibility of a `Gin(b/W)` bond (`b > 0`) and of the
unabsorbed pencil `H - E` (`κ ≡ 0`, needs the GUE density, `0 < b < 1/2`).
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

/-- **(a)** Positive absorption at the times `(r-i)/W` of the blocks of the length-`r` path makes
the path pencil invertible along every sample with Hermitian blocks. -/
theorem isUnit_pathPencil_of_pos (E : ℝ) (κ : ℝ → ℝ) (r : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian)
    (hκ : ∀ i : Fin r, 0 < κ (((r - i.val : ℕ) : ℝ) / W)) :
    IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω)) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_pathPencil E _ ω hA]
  refine Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr ?_
  have hW : (0 : ℝ) < W := Nat.cast_pos.mpr (Fin.pos x.2)
  exact div_pos (hκ x.1) (pow_pos hW 2)

/-- (a), pointwise form: `κ > 0` everywhere. -/
theorem isUnit_pathPencil_of_forall_pos (E : ℝ) (κ : ℝ → ℝ) (r : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hκ : ∀ s, 0 < κ s) :
    IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω)) :=
  isUnit_pathPencil_of_pos E κ r ω hA fun _ => hκ _

/-- **(c)** `z - X_r` is invertible along a passive sample, for every `κ ≥ 0`. -/
theorem isUnit_nearPencil_absorbed {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathNearSchur b E κ W r ω) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hp : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathNearSchur b E κ W r ω =
    portPencil (pathNearSchur b E κ W r ω) (boundaryZ b E) := rfl
  rw [hp, matrixImaginaryPart_portPencil_general, sub_eq_add_neg, add_comm]
  exact Matrix.PosDef.posSemidef_add (pathNearSchur_passive h r) (Matrix.PosDef.one.smul h.height)

/-- **(b)**, Schur form: for Hermitian `A`, passive `X` (`-Im X ⪰ 0`), `Im z > 0` and invertible
`B`, `A - E - X - z⁻¹BBᴴ` is invertible: its imaginary part is `Y + (Im z/|z|²) BBᴴ ≻ 0`. -/
theorem isUnit_freshPencil (b E : ℝ) (X A B : Matrix (Fin W) (Fin W) ℂ) (hA : A.IsHermitian)
    (hY : (passiveY X).PosSemidef) (hη : 0 < (boundaryZ b E).im) (hB : IsUnit B) :
    IsUnit (A - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (B * Bᴴ)) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hAE : (A - (E : ℂ) • 1).IsHermitian := hA.sub (by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal])
  rw [matrixImaginaryPart_sub, matrixImaginaryPart_sub, matrixImaginaryPart_hermitian _ hAE,
    matrixImaginaryPart_smul_hermitian _ _ (Matrix.isHermitian_mul_conjTranspose_self B),
    Complex.inv_im, zero_sub, sub_eq_add_neg, ← neg_smul]
  have hpos : (0 : ℂ) < ((-(-(boundaryZ b E).im / Complex.normSq (boundaryZ b E)) : ℝ) : ℂ) := by
    rw [Complex.zero_lt_real, neg_div, neg_neg]
    exact div_pos hη (Complex.normSq_pos.mpr fun h0 => by rw [h0] at hη; simp at hη)
  have hBB : (B * Bᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self B (Matrix.vecMul_injective_iff_isUnit.mpr hB)
  have := Matrix.PosDef.posSemidef_add hY (hBB.smul hpos)
  simpa [passiveY] using this

/-- **(b)**: the fresh layer matrix `[[A - E - X, B],[Bᴴ, z]]` (Layers' `layerMatrix`) is
invertible for Hermitian `A`, passive `X`, `Im z > 0` and invertible fresh bond `B`. -/
theorem isUnit_layerMatrix_fresh (b E : ℝ) (X A B : Matrix (Fin W) (Fin W) ℂ)
    (hA : A.IsHermitian) (hY : (passiveY X).PosSemidef) (hη : 0 < (boundaryZ b E).im)
    (hB : IsUnit B) :
    IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2)
      ((fun _ => A, fun _ _ => B) : LayerSample W .oneBlockOnePort)) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hz1 : IsUnit (boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hz).pow _
  let : Invertible (boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) :=
    hz1.invertible
  have hinv : ⅟(boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) =
      (boundaryZ b E)⁻¹ • 1 := by
    rw [invOf_eq_nonsing_inv]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ hz, one_smul]
  rw [layerMatrix, Matrix.isUnit_fromBlocks_iff_of_invertible₂₂, hinv,
    Matrix.isUnit_iff_isUnit_det]
  let e : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm
  rw [← Matrix.det_submatrix_equiv_self e]
  have hS : (BlockBand.Internal.Contracts.Layers.blockDiag (fun _ : Fin 1 => A) - (E : ℂ) • 1 -
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) -
      bondMatrix LayerShape.oneBlockOnePort (fun _ _ => B) * ((boundaryZ b E)⁻¹ • 1) *
        (bondMatrix LayerShape.oneBlockOnePort (fun _ _ => B))ᴴ).submatrix e e =
      A - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (B * Bᴴ) := by
    ext x y
    simp [e, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident,
      Matrix.one_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
      Fintype.sum_prod_type]
  rw [hS, ← Matrix.isUnit_iff_isUnit_det]
  exact isUnit_freshPencil b E X A B hA hY hη hB

/-- **(b) along the path**: the hypothesis `hG` of `boundaryToInterior_succ`, `pathCurrent_succ`
and `tagResponse_succ` holds whenever the fresh bond `B_{j+1}` is invertible (unabsorbed path,
Hermitian blocks, `Im z > 0`). -/
theorem isUnit_freshLayer_path {b E : ℝ} {ω : GrowthPath W} (h : PassiveSample b E (fun _ => 0) ω)
    (j : ℕ) (hB : IsUnit (ω.2 (j + 1))) :
    IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω)) :=
  isUnit_layerMatrix_fresh b E _ (ω.1 j) (ω.2 (j + 1)) (h.herm j) (pathNearSchur_passive h j)
    h.height hB

end BlockBand.Transmission.Bridge
