module

public import BlockBand.SourceProcess.ClosedSum.PerfPencil

/-!
# One near-end growth step of the modified pencil (Schur factorization)

Newest block first (`headEquiv`), for every `j`:
`modPencil_{j+1} ≅ [[A_j - E - L_j, C_nᴴ], [C_n, modPencil^{u=0}_j]]`, with the head load
`L_j = u B_{j+1}B_{j+1}ᴴ + [j = 0] v B_0B_0ᴴ` (`modPencil_succ_submatrix`). Hence
`det modPencil_{j+1} = det K_j · det(A_j - E - L_j - C_nᴴK_j⁻¹C_n)` when `K_j = modPencil^{u=0}_j`
is invertible (`det_modPencil_succ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge

variable {W : ℕ}

/-- The load of the newest block: `u B_{j+1}B_{j+1}ᴴ + [j = 0] v B_0B_0ᴴ`. -/
def headLoad (u v : ℂ) (j : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  u • (ω.2 (j + 1) * (ω.2 (j + 1))ᴴ) + if j = 0 then v • (ω.2 0 * (ω.2 0)ᴴ) else 0

theorem portLoad_pathAt_apply (u v : ℂ) (r : ℕ) (ω : GrowthPath W) (x y : Fin r × Fin W) :
    portLoad u v (pathAt W r ω) x y =
      (if x.1.val = 0 ∧ y.1.val = 0 then u * (ω.2 r * (ω.2 r)ᴴ) x.2 y.2 else 0) +
        (if x.1.val + 1 = r ∧ y.1.val + 1 = r then v * (ω.2 0 * (ω.2 0)ᴴ) x.2 y.2 else 0) := by
  have e0 : colOf (pathPortCoupling (pathAt W r ω)) 0 = nearCol W r ω := rfl
  have e1 : colOf (pathPortCoupling (pathAt W r ω)) 1 = farCol W r ω := rfl
  simp only [portLoad, e0, e1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply,
    conjTranspose_apply, nearCol_apply, farCol_apply]
  congr 1
  · by_cases h1 : x.1.val = 0 <;> by_cases h2 : y.1.val = 0 <;> simp [h1, h2]
  · by_cases h1 : x.1.val + 1 = r <;> by_cases h2 : y.1.val + 1 = r <;> simp [h1, h2]

theorem portLoad_succ_submatrix (u v : ℂ) (j : ℕ) (ω : GrowthPath W) :
    (portLoad u v (pathAt W (j + 1) ω)).submatrix (headEquiv j W) (headEquiv j W) =
      Matrix.fromBlocks (headLoad u v j ω) 0 0 (portLoad 0 v (pathAt W j ω)) := by
  ext (a | ⟨i, a⟩) (c | ⟨k, c⟩)
  · simp only [submatrix_apply, headEquiv_inl, portLoad_pathAt_apply, fromBlocks_apply₁₁,
      headLoad, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hj : j = 0 <;> simp [hj]
  · have := k.isLt
    simp only [submatrix_apply, headEquiv_inl, headEquiv_inr, portLoad_pathAt_apply,
      fromBlocks_apply₁₂, Matrix.zero_apply, Fin.val_succ]
    simp; omega
  · have := i.isLt
    simp only [submatrix_apply, headEquiv_inl, headEquiv_inr, portLoad_pathAt_apply,
      fromBlocks_apply₂₁, Matrix.zero_apply, Fin.val_succ]
    simp; omega
  · simp only [submatrix_apply, headEquiv_inr, portLoad_pathAt_apply, fromBlocks_apply₂₂,
      Fin.val_succ]
    simp

theorem modPencil_succ_submatrix (E : ℝ) (u v : ℂ) (j : ℕ) (ω : GrowthPath W) :
    (modPencil E u v (pathAt W (j + 1) ω)).submatrix (headEquiv j W) (headEquiv j W) =
      Matrix.fromBlocks (ω.1 j - (E : ℂ) • 1 - headLoad u v j ω) (nearCol W j ω)ᴴ (nearCol W j ω)
        (modPencil E 0 v (pathAt W j ω)) := by
  have hH := pathMatrix_succ_submatrix E j ω
  have hL := portLoad_succ_submatrix u v j ω
  ext x y
  have h1 := congrFun (congrFun hH x) y
  have h2 := congrFun (congrFun hL x) y
  simp only [submatrix_apply] at h1 h2 ⊢
  rw [modPencil_apply, h1, h2]
  rcases x with a | a <;> rcases y with c | c <;> simp [modPencil_apply]

/-- **Schur factorization of one growth step.** -/
theorem det_modPencil_succ (E : ℝ) (u v : ℂ) (j : ℕ) (ω : GrowthPath W)
    (hK : IsUnit (modPencil E 0 v (pathAt W j ω))) :
    (modPencil E u v (pathAt W (j + 1) ω)).det = (modPencil E 0 v (pathAt W j ω)).det *
      (ω.1 j - (E : ℂ) • 1 - headLoad u v j ω -
        (nearCol W j ω)ᴴ * (modPencil E 0 v (pathAt W j ω))⁻¹ * nearCol W j ω).det := by
  let : Invertible (modPencil E 0 v (pathAt W j ω)) := hK.invertible
  rw [← Matrix.det_submatrix_equiv_self (headEquiv j W), modPencil_succ_submatrix,
    Matrix.det_fromBlocks₂₂, invOf_eq_nonsing_inv]

end BlockBand.SourceProcess.ClosedSum
