module

public import BlockBand.Transmission.PassiveCovariance.DressedTrace

/-!
# `U = LL*` is a dressed word

The bilinear forms of the fresh transport `U = LL*` are dressed bilinear forms:
`v₁*(LL*)v₂ = (ι₁v₁)*K̂𝒢P₂(K̂𝒢)ᴴ(ι₁v₂)` (`freshU_wordForm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `ι₁v`: a `W`-vector on the physical sites, zero on the port. -/
def physVec (v : Fin W → ℂ) : LayerSite W .oneBlockOnePort → ℂ :=
  Sum.elim (fun u => v u.2) fun _ => 0

/-- The port projector `P₂ = diag(0, I)`. -/
def portProj : LayerMat W := fromBlocks 0 0 0 1

theorem physVec_comp0 (v : Fin W → ℂ) : physVec v ∘ siteOf 0 = v := by
  funext x; rfl

theorem physVec_comp1 (v : Fin W → ℂ) : physVec v ∘ siteOf 1 = 0 := by
  funext x; rfl

theorem vecNorm_physVec (v : Fin W → ℂ) : vecNorm (physVec v) = vecNorm v := by
  rw [vecNorm, vecNorm, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [physVec]

theorem norm_portProj_le : ‖(portProj : LayerMat W)‖ ≤ 1 := by
  refine (norm_fromBlocks_le _ _ _ _).trans ?_
  simp only [norm_zero, zero_add]
  exact norm_one_matrix_le

theorem blkAt_portProj (t u : Fin 2) :
    blkAt (portProj : LayerMat W) t u = if t = 1 ∧ u = 1 then 1 else 0 := by
  fin_cases t <;> fin_cases u <;> ext x y <;> simp [blkAt, siteOf, portProj, Matrix.one_apply]

theorem bilinear_zero_left {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    bilinear 0 M v = 0 := by simp [bilinear]

/-- **`v₁*(LL*)v₂` is the dressed bilinear form `(ι₁v₁)*K̂𝒢P₂(K̂𝒢)ᴴ(ι₁v₂)`.** -/
theorem freshU_wordForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (v₁ v₂ : Fin W → ℂ) :
    bilinear v₁ (freshU b E X ω) v₂ =
      wordForm (kHat b E X) (physVec v₁) (physVec v₂) ![1, 3] ![1, portProj, 1] (gRes b E X ω) := by
  set G := gRes b E X ω
  have hM : wordVal (kHat b E X) G ![1, 3] ![1, portProj, 1] =
      wLetter (kHat b E X) G 1 * (portProj * wLetter (kHat b E X) G 3) := by
    rw [wordVal_succ, wordVal_succ, wordVal_zero]
    simp
  have h01 : blkAt (wLetter (kHat b E X) G 1) 0 1 = lAt E (boundaryZ b E) X ω := by
    rw [blkAt_wLetter]; rfl
  have h10 : blkAt (wLetter (kHat b E X) G 3) 1 0 = (lAt E (boundaryZ b E) X ω)ᴴ := by
    rw [blkAt_wLetter]; rfl
  have c0 : ((0 : Fin 2) = 1) = False := by decide
  have hblk : blkAt (wordVal (kHat b E X) G ![1, 3] ![1, portProj, 1]) 0 0 = freshU b E X ω := by
    rw [hM, blkAt_mul, Fin.sum_univ_two, blkAt_mul, blkAt_mul, Fin.sum_univ_two, Fin.sum_univ_two,
      blkAt_portProj, blkAt_portProj, blkAt_portProj, blkAt_portProj]
    simp only [c0, and_false, false_and, and_self, ↓reduceIte, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero, h01, h10]
    rfl
  rw [wordForm, wordForm_blocks, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hblk,
    physVec_comp0, physVec_comp0, physVec_comp1, physVec_comp1]
  simp [bilinear]

end BlockBand.Transmission.PassiveCovariance
