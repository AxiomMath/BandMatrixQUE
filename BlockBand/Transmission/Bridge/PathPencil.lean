module

public import BlockBand.Transmission.Bridge.Fresh

/-!
# The path pencil of the near-end-grown path and its one-block decomposition

For the path `pathAt W r ω` with absorption `ε = layerAbsorption W κ r` we write
`F_r = H_path - E + i diag ε` (`pathPencil`), `C_n, C_f` for the near/far columns of the port
coupling (`nearCol`, `farCol`), and `F̃_r = F_r - z⁻¹ C_f C_fᴴ` for the pencil with the far
matched lead eliminated (`leadPencil`). For `r ≥ 1`, putting the newest block (position `0`)
first (`headEquiv`), `F̃_{r+1}` is the block matrix `[[A_r - E + iε₀, C_nᴴ], [C_n, F̃_r]]`
(`leadPencil_succ_submatrix`) and `C_n^{(r+1)}` is `[B_{r+1}; 0]` (`nearCol_succ_submatrix`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped Matrix

variable {W : ℕ}

/-- Near column `C_n` (port `0`) of the port coupling of `pathAt W r ω`. -/
def nearCol (W r : ℕ) (ω : GrowthPath W) : Matrix (Fin r × Fin W) (Fin W) ℂ :=
  fun a y => pathPortCoupling (pathAt W r ω) a (0, y)

/-- Far column `C_f` (port `1`) of the port coupling of `pathAt W r ω`. -/
def farCol (W r : ℕ) (ω : GrowthPath W) : Matrix (Fin r × Fin W) (Fin W) ℂ :=
  fun a y => pathPortCoupling (pathAt W r ω) a (1, y)

/-- The pencil `F = H_path - E + i diag ε`. -/
def pathPencil {r : ℕ} (E : ℝ) (ε : Fin r → ℝ) (p : PathSample W r) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  pathMatrix p - (E : ℂ) • 1 + absorptionDiag W ε

/-- The pencil of `pathAt W r ω` with its far matched lead eliminated,
`F̃_r = F_r - z⁻¹ C_f C_fᴴ`. -/
def leadPencil (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  pathPencil E (layerAbsorption W κ r) (pathAt W r ω) -
    (boundaryZ b E)⁻¹ • (farCol W r ω * (farCol W r ω)ᴴ)

theorem nearCol_apply (r : ℕ) (ω : GrowthPath W) (a : Fin r × Fin W) (y : Fin W) :
    nearCol W r ω a y = if a.1.val = 0 then ω.2 r a.2 y else 0 := by
  simp [nearCol, pathPortCoupling, pathAt]

theorem farCol_apply (r : ℕ) (ω : GrowthPath W) (a : Fin r × Fin W) (y : Fin W) :
    farCol W r ω a y = if a.1.val + 1 = r then ω.2 0 a.2 y else 0 := by
  simp [farCol, pathPortCoupling, pathAt]

theorem pathMatrix_pathAt_apply (r : ℕ) (ω : GrowthPath W) (x y : Fin r × Fin W) :
    pathMatrix (pathAt W r ω) x y =
      if x.1 = y.1 then ω.1 (r - 1 - x.1.val) x.2 y.2
      else if x.1.val + 1 = y.1.val then star (ω.2 (r - 1 - x.1.val) y.2 x.2)
      else if y.1.val + 1 = x.1.val then ω.2 (r - 1 - y.1.val) x.2 y.2
      else 0 := by
  unfold pathMatrix pathAt
  split_ifs <;> simp [Matrix.conjTranspose_apply]

/-- The port blocks of the absorbed two-port Schur matrix are the column congruences
`(𝕏)_{ij} = C_iᴴ F⁻¹ C_j`. -/
theorem portBlock_absorbedPathSchur (E : ℝ) (κ : ℝ → ℝ) (r : ℕ) (ω : GrowthPath W) (i j : Fin 2) :
    portBlock (absorbedPathSchur E (layerAbsorption W κ r) (pathAt W r ω)) i j =
      (Matrix.of fun a y => pathPortCoupling (pathAt W r ω) a (i, y) :
        Matrix (Fin r × Fin W) (Fin W) ℂ)ᴴ *
        (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))⁻¹ *
        (Matrix.of fun a y => pathPortCoupling (pathAt W r ω) a (j, y)) := by
  ext x y
  simp [portBlock, absorbedPathSchur, pathPencil, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Positions of the length-`r+1` path with the newest block (position `0`) split off. -/
def headEquiv (r W : ℕ) : Fin W ⊕ (Fin r × Fin W) ≃ Fin (r + 1) × Fin W where
  toFun
    | Sum.inl x => (0, x)
    | Sum.inr p => (p.1.succ, p.2)
  invFun p := Fin.cases (motive := fun _ => Fin W ⊕ (Fin r × Fin W)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv := by rintro (x | ⟨i, x⟩) <;> simp
  right_inv := by
    rintro ⟨i, x⟩
    induction i using Fin.cases <;> simp

theorem headEquiv_inl (r : ℕ) (x : Fin W) : headEquiv r W (Sum.inl x) = (0, x) := rfl

theorem headEquiv_inr (r : ℕ) (i : Fin r) (x : Fin W) :
    headEquiv r W (Sum.inr (i, x)) = (i.succ, x) := rfl

theorem farCol_succ_inl {r : ℕ} (hr : 1 ≤ r) (ω : GrowthPath W) (x y : Fin W) :
    farCol W (r + 1) ω (0, x) y = 0 := by
  rw [farCol_apply]; simp; omega

theorem farCol_succ_inr (r : ℕ) (ω : GrowthPath W) (i : Fin r) (x y : Fin W) :
    farCol W (r + 1) ω (i.succ, x) y = farCol W r ω (i, x) y := by
  rw [farCol_apply, farCol_apply]; simp

/-- The near column of the length-`r+1` path, newest block first, is `[B_{r+1}; 0]`. -/
theorem nearCol_succ_submatrix (r : ℕ) (ω : GrowthPath W) :
    (nearCol W (r + 1) ω).submatrix (headEquiv r W) id = Matrix.fromRows (ω.2 (r + 1)) 0 := by
  ext (x | ⟨i, x⟩) y <;> simp [nearCol_apply, headEquiv_inl, headEquiv_inr]

/-- **One-block decomposition of the lead-closed pencil**: for `r ≥ 1`,
`F̃_{r+1} = [[A_r - E + iε₀, C_nᴴ], [C_n, F̃_r]]` with the newest block first, where `C_n` is the
near column of the length-`r` path (`= B_r` on its position `0`) and `ε₀ = κ((r+1)/W)/W²`. -/
theorem leadPencil_succ_submatrix (b E : ℝ) (κ : ℝ → ℝ) {r : ℕ} (hr : 1 ≤ r) (ω : GrowthPath W) :
    (leadPencil b E κ W (r + 1) ω).submatrix (headEquiv r W) (headEquiv r W) =
      Matrix.fromBlocks
        (ω.1 r - (E : ℂ) • 1 + (((layerAbsorption W κ (r + 1) 0 : ℝ) : ℂ) * Complex.I) • 1)
        (nearCol W r ω)ᴴ (nearCol W r ω) (leadPencil b E κ W r ω) := by
  have hsub : ∀ i : Fin r, r + 1 - 1 - (i.val + 1) = r - 1 - i.val := fun i => by omega
  ext (x | ⟨i, x⟩) (y | ⟨j, y⟩)
  · simp [leadPencil, pathPencil, pathMatrix_pathAt_apply, absorptionDiag, headEquiv_inl,
      Matrix.mul_apply, farCol_succ_inl hr, Matrix.one_apply, Matrix.diagonal_apply]
  · simp [leadPencil, pathPencil, pathMatrix_pathAt_apply, absorptionDiag, headEquiv_inl,
      headEquiv_inr, Matrix.mul_apply, farCol_succ_inl hr, Matrix.one_apply,
      Matrix.diagonal_apply, nearCol_apply, Matrix.conjTranspose_apply]
    split_ifs <;> simp_all [Fin.ext_iff]
  · simp [leadPencil, pathPencil, pathMatrix_pathAt_apply, absorptionDiag, headEquiv_inl,
      headEquiv_inr, Matrix.mul_apply, farCol_succ_inl hr, nearCol_apply]
  · simp only [leadPencil, pathPencil, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, headEquiv_inr, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Matrix.conjTranspose_apply, farCol_succ_inr, pathMatrix_pathAt_apply, Fin.succ_inj,
      Fin.val_succ, hsub, absorptionDiag, Matrix.diagonal_apply, Matrix.one_apply,
      Prod.mk.injEq, layerAbsorption]
    congr 2
    · split_ifs <;> first | rfl | omega
    · rw [show r + 1 - ((i : ℕ) + 1) = r - (i : ℕ) by omega]

end BlockBand.Transmission.Bridge
