module

public import BlockBand.Transmission.Bridge.FreshIdentity

/-!
# The near-end growth step of the two-input path is transported by `N`

Linear-system and block lemmas for `boundaryToInterior_succ`: for `j ≥ 1`, with
`N = freshTransport b E 𝕏_j (freshSample W j ω)` (the one-layer transport at
`𝕏_j = pathSchur E (pathAt W j ω)`), the boundary-to-interior map of the length-`j+1` path is,
newest block first, `𝒰_{j+1} = [ι*ℝ_j N ; 𝒰_j N]` (so its old rows are `𝒰_j N`), and
`ℝ_{j+1} = z⁻¹(1 - C'ᴴ𝒰_{j+1})`. Consequently `Y_{j+1;k} = Nᴴ Y_{j;k} N` for every old tag
(`tagResponse_succ`). The new row `ι*ℝ_jN = D₊` and the new-tag injection
`Y_{j+1;j} = D₊ᴴD₊` are `boundaryToInterior_succ_newRow` and `tagResponse_succ_new`.
Hypotheses: Hermitian blocks, `Im z > 0`, `H_j - E`, `H_{j+1} - E` and the fresh layer matrix
invertible; the last one is discharged when `B_{j+1}` is invertible (`isUnit_freshLayer_path`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix

variable {W : ℕ}

/-!
## The two-lead linear system
-/

theorem full_solution (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω)) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) * boundaryToInterior b E W n ω +
        pathPortCoupling (pathAt W n ω) * boundaryResolvent b E W n ω = 0 ∧
      (pathPortCoupling (pathAt W n ω))ᴴ * boundaryToInterior b E W n ω +
        boundaryZ b E • boundaryResolvent b E W n ω = 1 := by
  have h := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  rw [← Matrix.fromBlocks_toBlocks (fullPathMatrix b E W n ω)⁻¹, fullPathMatrix,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  refine ⟨h.2.1, ?_⟩
  have h4 := h.2.2.2
  rwa [Matrix.smul_mul, Matrix.one_mul] at h4

theorem full_unique (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω))
    (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (h1 : (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) * U + pathPortCoupling (pathAt W n ω) * R = 0)
    (h2 : (pathPortCoupling (pathAt W n ω))ᴴ * U + boundaryZ b E • R = 1) :
    U = boundaryToInterior b E W n ω ∧ R = boundaryResolvent b E W n ω := by
  have hMU : fullPathMatrix b E W n ω * Matrix.fromRows U R = Matrix.fromRows
      (0 : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
    unfold fullPathMatrix
    rw [Matrix.fromBlocks_mul_fromRows, h1, Matrix.smul_mul, Matrix.one_mul, h2]
  have hinv : (fullPathMatrix b E W n ω)⁻¹ * fullPathMatrix b E W n ω = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  have : Matrix.fromRows U R = (fullPathMatrix b E W n ω)⁻¹ * Matrix.fromRows
      (0 : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
    rw [← hMU, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [← Matrix.fromBlocks_toBlocks (fullPathMatrix b E W n ω)⁻¹,
    Matrix.fromBlocks_mul_fromRows] at this
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add] at this
  exact Matrix.fromRows_inj this

theorem isUnit_fullPathMatrix (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    IsUnit (fullPathMatrix b E W n ω) := by
  let : Invertible (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) := hF.invertible
  rw [fullPathMatrix, Matrix.isUnit_fromBlocks_iff_of_invertible₁₁, invOf_eq_nonsing_inv]
  exact portPencil_isUnit _ (pathSchur_isHermitian E n ω hA) hη

/-!
## Block structure of the grown path
-/

/-- The far part of the port coupling (port `1` columns only). -/
def farCoupling (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin j × Fin W) (Fin 2 × Fin W) ℂ :=
  fun p c => if c.1 = 1 then pathPortCoupling (pathAt W j ω) p c else 0

theorem coupling_split (j : ℕ) (ω : GrowthPath W) :
    pathPortCoupling (pathAt W j ω) = nearCol W j ω * nearSel W + farCoupling W j ω := by
  ext p ⟨i, y⟩
  fin_cases i <;> simp [nearCol, farCoupling, nearSel, Matrix.mul_apply]

theorem nearSel_mul_conjTranspose : nearSel W * (nearSel W)ᴴ = 1 := by
  ext x y
  simp [nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem nearSel_mul_farCoupling (j : ℕ) (ω : GrowthPath W) :
    nearSel W * (farCoupling W j ω)ᴴ = 0 := by
  ext x p
  simp [nearSel, farCoupling, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem farCoupling_mul_freshTransport (b E : ℝ) (j : ℕ) (ω : GrowthPath W)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω' : LayerSample W .oneBlockOnePort) :
    farCoupling W j ω * freshTransport b E XX ω' = farCoupling W j ω := by
  ext p ⟨i, y⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> simp [farCoupling, freshTransport, Matrix.one_apply]

theorem pathMatrix_succ_submatrix (E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1).submatrix (headEquiv j W) (headEquiv j W) =
      Matrix.fromBlocks (ω.1 j - (E : ℂ) • 1) (nearCol W j ω)ᴴ (nearCol W j ω)
        (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) := by
  have hsub : ∀ i : Fin j, j + 1 - 1 - (i.val + 1) = j - 1 - i.val := fun i => by omega
  ext (x | ⟨i, x⟩) (y | ⟨k, y⟩)
  · simp [pathMatrix_pathAt_apply, headEquiv_inl, Matrix.one_apply]
  · simp [pathMatrix_pathAt_apply, headEquiv_inl, headEquiv_inr, Matrix.one_apply, nearCol_apply,
      Matrix.conjTranspose_apply]
    split_ifs <;> simp_all [Fin.ext_iff]
  · simp [pathMatrix_pathAt_apply, headEquiv_inl, headEquiv_inr, nearCol_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, headEquiv_inr,
      Matrix.fromBlocks_apply₂₂, pathMatrix_pathAt_apply, Fin.succ_inj, Fin.val_succ, hsub,
      Matrix.one_apply, Prod.mk.injEq, add_left_inj]

theorem coupling_succ_submatrix {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W) :
    (pathPortCoupling (pathAt W (j + 1) ω)).submatrix (headEquiv j W) id =
      Matrix.fromRows (ω.2 (j + 1) * nearSel W) (farCoupling W j ω) := by
  ext (x | ⟨i, x⟩) ⟨c, y⟩ <;> fin_cases c
  · simp [pathPortCoupling, pathAt, headEquiv_inl, nearSel, Matrix.mul_apply]
  · simp [pathPortCoupling, pathAt, headEquiv_inl, nearSel, Matrix.mul_apply]; omega
  · simp [pathPortCoupling, pathAt, headEquiv_inr, farCoupling]
  · simp [pathPortCoupling, pathAt, headEquiv_inr, farCoupling]

end BlockBand.Transmission.Bridge
