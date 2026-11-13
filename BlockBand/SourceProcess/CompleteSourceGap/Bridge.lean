module

public import BlockBand.SourceProcess.CompleteSourceGap.Interface
public import BlockBand.Transmission.Bridge.Complete

/-!
# The owed bridge: `freshTwoPortSchur` along the near-end-grown path

Main results:
* `pathSchur_succ_eq_freshTwoPortSchur`: for `j ≥ 1`, if `H_j - E` and `H_{j+1} - E` are
  invertible, `𝕏_{j+1} = freshTwoPortSchur E 𝕏_j (freshSample W j ω)`, `𝕏_j = pathSchur E (pathAt W j ω)`;
* `ae_pathSchur_succ_eq_freshTwoPortSchur`: the same almost surely, every `j ≥ 1`
  (`0 < b < 1/2`... only `b < 1/2` and `W ≥ 1` are used);
* `separatorMatrix_eq_sepOf`: TS `separatorMatrix` along the path is `sepOf` at `𝕏_j`.

Proof: newest block first (`headEquiv`), `H_{j+1} - E = [[A_j - E, C_nᴴ], [C_n, H_j - E]]`
(`pathMatrix_succ_submatrix`) and the coupling is `[B_{j+1}ι*; C_far]`
(`coupling_succ_submatrix`); the block inverse with invertible `H_j - E` has Schur complement
`A_j - E - 𝕏₀₀`, and the four port blocks of `C*(H_{j+1} - E)⁻¹C` are those of `𝕏₊`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped Matrix

variable {W : ℕ}

/-- Port column `i` of a coupling `C : n × 2W`. -/
def portCol {n : Type*} (C : Matrix n (Fin 2 × Fin W) ℂ) (i : Fin 2) : Matrix n (Fin W) ℂ :=
  Matrix.of fun a y => C a (i, y)

theorem portBlock_sandwich {n : Type*} [Fintype n] (C : Matrix n (Fin 2 × Fin W) ℂ)
    (M : Matrix n n ℂ) (i k : Fin 2) :
    portBlock (Cᴴ * M * C) i k = (portCol C i)ᴴ * M * portCol C k := by
  ext x y
  simp [portBlock, portCol, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem portBlock_ofPortBlocks (M₀₀ M₀₁ M₁₀ M₁₁ : Matrix (Fin W) (Fin W) ℂ) (i k : Fin 2) :
    portBlock (ofPortBlocks M₀₀ M₀₁ M₁₀ M₁₁) i k = ![![M₀₀, M₀₁], ![M₁₀, M₁₁]] i k := by
  ext x y; rfl

theorem portBlock_ext' {M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h : ∀ i k, portBlock M i k = portBlock N i k) : M = N := by
  ext ⟨i, x⟩ ⟨k, y⟩; exact congrFun (congrFun (h i k) x) y

/-- Sandwich of a block matrix between two row-stacked couplings. -/
theorem fromRows_sandwich {m n k : Type*} [Fintype m] [Fintype n]
    (p : Matrix m k ℂ) (q : Matrix n k ℂ) (a : Matrix m m ℂ) (b : Matrix m n ℂ)
    (c : Matrix n m ℂ) (d : Matrix n n ℂ) :
    (Matrix.fromRows p q)ᴴ * Matrix.fromBlocks a b c d * Matrix.fromRows p q =
      pᴴ * a * p + pᴴ * b * q + (qᴴ * c * p + qᴴ * d * q) := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- Totalized block inverse with invertible bottom-right block and invertible whole matrix. -/
theorem inv_fromBlocks_of₂₂ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D) (hM : IsUnit (Matrix.fromBlocks A B C D)) :
    (Matrix.fromBlocks A B C D)⁻¹ =
      Matrix.fromBlocks (A - B * D⁻¹ * C)⁻¹ (-((A - B * D⁻¹ * C)⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹))
        (D⁻¹ + D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹ * B * D⁻¹) := by
  let : Invertible D := hD.invertible
  have hS : IsUnit (A - B * ⅟D * C) := (isUnit_fromBlocks_iff_of_invertible₂₂).mp hM
  let : Invertible (A - B * ⅟D * C) := hS.invertible
  let : Invertible (Matrix.fromBlocks A B C D) := hM.invertible
  have h := invOf_fromBlocks₂₂_eq A B C D
  simp only [invOf_eq_nonsing_inv] at h
  exact h

theorem portCol_fromRows {m n : Type*} (p : Matrix m (Fin 2 × Fin W) ℂ)
    (q : Matrix n (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    portCol (Matrix.fromRows p q) i = Matrix.fromRows (portCol p i) (portCol q i) := by
  ext (a | a) y <;> rfl

theorem portCol_near (B : Matrix (Fin W) (Fin W) ℂ) (i : Fin 2) :
    portCol (B * nearSel W) i = if i = 0 then B else 0 := by
  ext x y; fin_cases i <;> simp [portCol, nearSel, Matrix.mul_apply]

theorem portCol_far (j : ℕ) (ω : GrowthPath W) (i : Fin 2) :
    portCol (farCoupling W j ω) i = if i = 1 then farCol W j ω else 0 := by
  ext x y; fin_cases i <;> simp [portCol, farCoupling, farCol]

theorem portCol_coupling_zero (j : ℕ) (ω : GrowthPath W) :
    portCol (pathPortCoupling (pathAt W j ω)) 0 = nearCol W j ω := rfl

theorem portCol_coupling_one (j : ℕ) (ω : GrowthPath W) :
    portCol (pathPortCoupling (pathAt W j ω)) 1 = farCol W j ω := rfl

/-- Port blocks of `𝕏_j`: `(𝕏_j)_{ik} = c_iᴴ (H_j - E)⁻¹ c_k`, `c₀ = C_n`, `c₁ = C_f`. -/
theorem portBlock_pathSchur (E : ℝ) (j : ℕ) (ω : GrowthPath W) (i k : Fin 2) :
    portBlock (pathSchur E (pathAt W j ω)) i k =
      (portCol (pathPortCoupling (pathAt W j ω)) i)ᴴ *
        (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)⁻¹ *
        portCol (pathPortCoupling (pathAt W j ω)) k := by
  rw [pathSchur, portBlock_sandwich]

/-- **The owed bridge** (deterministic): for `j ≥ 1`, with `H_j - E` and `H_{j+1} - E`
invertible, `𝕏_{j+1} = freshTwoPortSchur E 𝕏_j (freshSample W j ω)`. -/
theorem pathSchur_succ_eq_freshTwoPortSchur (E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1)) :
    pathSchur E (pathAt W (j + 1) ω) =
      freshTwoPortSchur E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  set e := headEquiv j W
  set F := pathMatrix (pathAt W j ω) - (E : ℂ) • 1
  set Cn := nearCol W j ω
  set Cf := farCol W j ω
  set S := ω.1 j - (E : ℂ) • 1 - Cnᴴ * F⁻¹ * Cn
  have hblk := pathMatrix_succ_submatrix E j ω
  have hcpl := coupling_succ_submatrix hj ω
  have hM : IsUnit (Matrix.fromBlocks (ω.1 j - (E : ℂ) • 1) Cnᴴ Cn F) := by
    rw [← hblk, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
      ← Matrix.isUnit_iff_isUnit_det]
    exact hF'
  have hre : pathSchur E (pathAt W (j + 1) ω) =
      ((pathPortCoupling (pathAt W (j + 1) ω)).submatrix e id)ᴴ *
        ((pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1).submatrix e e)⁻¹ *
        (pathPortCoupling (pathAt W (j + 1) ω)).submatrix e id := by
    rw [pathSchur, Matrix.inv_submatrix_equiv, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  rw [hre, hblk, hcpl, inv_fromBlocks_of₂₂ _ _ _ _ hF hM, fromRows_sandwich]
  have h00 : portBlock (pathSchur E (pathAt W j ω)) 0 0 = Cnᴴ * F⁻¹ * Cn := portBlock_pathSchur E j ω 0 0
  have h01 : portBlock (pathSchur E (pathAt W j ω)) 0 1 = Cnᴴ * F⁻¹ * Cf := portBlock_pathSchur E j ω 0 1
  have h10 : portBlock (pathSchur E (pathAt W j ω)) 1 0 = Cfᴴ * F⁻¹ * Cn := portBlock_pathSchur E j ω 1 0
  have h11 : portBlock (pathSchur E (pathAt W j ω)) 1 1 = Cfᴴ * F⁻¹ * Cf := portBlock_pathSchur E j ω 1 1
  have hG : (ω.1 j - (E : ℂ) • 1 - portBlock (pathSchur E (pathAt W j ω)) 0 0)⁻¹ = S⁻¹ := by
    rw [h00]
  apply portBlock_ext'
  intro i k
  have hP : ∀ (P Q : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (R : Matrix (Fin j × Fin W) (Fin 2 × Fin W) ℂ)
      (T : Matrix (Fin j × Fin W) (Fin 2 × Fin W) ℂ) (a : Matrix (Fin W) (Fin W) ℂ)
      (b : Matrix (Fin W) (Fin j × Fin W) ℂ) (c : Matrix (Fin j × Fin W) (Fin W) ℂ)
      (d : Matrix (Fin j × Fin W) (Fin j × Fin W) ℂ),
      portBlock (Pᴴ * a * P + Pᴴ * b * R + (Rᴴ * c * P + Rᴴ * d * R)) i k =
        (portCol P i)ᴴ * a * portCol P k + (portCol P i)ᴴ * b * portCol R k +
          ((portCol R i)ᴴ * c * portCol P k + (portCol R i)ᴴ * d * portCol R k) := by
    intro P Q R T a b c d
    ext x y
    simp [portBlock, portCol, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hP (ω.2 (j + 1) * nearSel W) 0 (farCoupling W j ω) 0, portCol_near, portCol_near, portCol_far,
    portCol_far]
  change _ = portBlock (ofPortBlocks _ _ _ _) i k
  rw [portBlock_ofPortBlocks]
  simp only [freshSample]
  rw [hG, h01, h10, h11]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, S, Cf]

/-- **The owed bridge**, almost surely (`b < 1/2`, `W ≥ 1`): for every `j ≥ 1`,
`𝕏_{j+1} = freshTwoPortSchur E 𝕏_j (freshSample W j ω)`. -/
theorem ae_pathSchur_succ_eq_freshTwoPortSchur {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j : ℕ, 1 ≤ j →
      pathSchur E (pathAt W (j + 1) ω) =
        freshTwoPortSchur E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E] with ω hω j hj
  exact pathSchur_succ_eq_freshTwoPortSchur E hj ω (hω j) (hω (j + 1))

/-- TS `separatorMatrix` along the path is `sepOf` at `𝕏_j` (given `H_j - E` invertible). -/
theorem separatorMatrix_eq_sepOf (b E : ℝ) (j : ℕ) (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)) (σ : Separator) :
    separatorMatrix b E W j ω σ = sepOf b E (pathSchur E (pathAt W j ω)) σ := by
  cases σ <;> simp [separatorMatrix, sepOf, scatteringMatrix_eq b E j ω hF]

end BlockBand.SourceProcess.CompleteSourceGap
