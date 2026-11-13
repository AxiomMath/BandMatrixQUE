module

public import BlockBand.QUE.Invariance.CyclicLaw
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Data.Matrix.Block

/-!
# The block-unitary embedding

A family of unitaries `U_k ∈ U(W)`, one per block, embeds as a block diagonal unitary on the
sites (in block-first order), continuously in the family; `blockUnitaryConjugation` is
conjugation by it.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open Matrix

/-- The block diagonal matrix, in physical block-first site order. -/
def blockUnitaryMatrix (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) : p.SiteMatrix :=
  (Matrix.blockDiagonal (fun k => (U k : Matrix (Fin p.W) (Fin p.W) ℂ))).submatrix
    (Equiv.prodComm (ZMod p.n) (Fin p.W)) (Equiv.prodComm (ZMod p.n) (Fin p.W))

@[simp] theorem blockUnitaryMatrix_apply (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (x y : p.Site) :
    p.blockUnitaryMatrix U x y = if x.1 = y.1 then U x.1 x.2 y.2 else 0 := rfl

/-- Block diagonal embedding varies continuously with the independent block rotations. -/
theorem continuous_blockUnitaryMatrix (p : BlockBand.Parameters) :
    Continuous (p.blockUnitaryMatrix) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  simp only [blockUnitaryMatrix_apply]
  split_ifs
  · have hev : Continuous (fun V : Matrix.unitaryGroup (Fin p.W) ℂ => V x.2 y.2) :=
      continuous_subtype_val.matrix_elem x.2 y.2
    exact hev.comp (continuous_apply x.1)
  · exact continuous_const

/-- The block diagonal embedding is unitary. -/
theorem blockUnitaryMatrix_mem (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    p.blockUnitaryMatrix U ∈ Matrix.unitaryGroup p.Site ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (p.blockUnitaryMatrix U)ᴴ * p.blockUnitaryMatrix U = 1
  unfold blockUnitaryMatrix
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hU : (fun k : ZMod p.n =>
      ((U k : Matrix (Fin p.W) (Fin p.W) ℂ)ᴴ *
        (U k : Matrix (Fin p.W) (Fin p.W) ℂ))) = 1 := by
    funext k
    exact Matrix.UnitaryGroup.star_mul_self (U k)
  rw [hU, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

/-- The block diagonal embedding as an element of the site unitary group. -/
def blockUnitary (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    Matrix.unitaryGroup p.Site ℂ := ⟨p.blockUnitaryMatrix U, p.blockUnitaryMatrix_mem U⟩

@[simp] theorem blockUnitary_coe (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    (p.blockUnitary U : p.SiteMatrix) = p.blockUnitaryMatrix U := rfl

/-- Physical conjugation by deterministic, independently chosen block unitaries. -/
def blockUnitaryConjugation (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (H : p.SiteMatrix) : p.SiteMatrix :=
  p.blockUnitaryMatrix U * H * (p.blockUnitaryMatrix U)ᴴ

end BlockBand.Parameters
