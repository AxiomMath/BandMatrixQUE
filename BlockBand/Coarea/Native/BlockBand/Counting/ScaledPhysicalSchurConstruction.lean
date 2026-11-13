module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledPhysicalProjectedWegner
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.BlockMatrix

/-!
# Physical singleton splitting for the scaled Schur construction

This module supplies the explicit reindexing and measurable full pencil needed before
Schur complementation.  It deliberately stops before claiming a completed
`ScaledPhysicalSchurMatrixData`: that final construction additionally needs the
parameter-dependent measurability of the nonsingular inverse of the complementary
block and the algebraic separation of the Schur complement into its Hermitian real
background and positive imaginary absorber.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The singleton `BlockGUE` index is canonically the site set in physical block `j`. -/
def singletonBlockSetSiteEquiv (p : Params) (j : ZMod p.n) :
    BlockGUE.Index (singletonBlockSize p.W) ≃
      BlockSetSite ({j} : Set (ZMod p.n)) p.W where
  toFun a := ⟨(j, a.2), by simp⟩
  invFun x := ⟨0, x.1.2⟩
  left_inv a := by
    apply Sigma.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv x := by
    apply Subtype.ext
    have hx : x.1.1 = j := by simpa using x.property
    exact Prod.ext hx.symm rfl

@[simp] theorem singletonBlockSetSiteEquiv_apply
    (p : Params) (j : ZMod p.n)
    (a : BlockGUE.Index (singletonBlockSize p.W)) :
    (singletonBlockSetSiteEquiv p j a).1 = (j, a.2) := rfl

/-- The physical site space split into the exposed singleton block and its complement. -/
def singletonPhysicalSplitEquiv (p : Params) (j : ZMod p.n) :
    BlockGUE.Index (singletonBlockSize p.W) ⊕
      BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W ≃ Site p.n p.W :=
  (Equiv.sumCongr (singletonBlockSetSiteEquiv p j) (Equiv.refl _)).trans
    (splitEquiv ({j} : Set (ZMod p.n)))

@[simp] theorem singletonPhysicalSplitEquiv_inl
    (p : Params) (j : ZMod p.n)
    (a : BlockGUE.Index (singletonBlockSize p.W)) :
    singletonPhysicalSplitEquiv p j (Sum.inl a) = (j, a.2) := rfl

/-- Full absorbed physical pencil reconstructed from exterior coordinates and a
normalized exposed matrix. -/
def physicalPencilFromExteriorNormalizedBlock
    (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ)
    (z : (exteriorUpperPairs p j → ℂ) ×
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  physicalMatrixFromExteriorNormalizedBlock p j z + V -
    (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
    Complex.I • (Γ + η • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))

/-- The reconstructed physical pencil is measurable in the exterior and exposed
coordinates. -/
theorem measurable_physicalPencilFromExteriorNormalizedBlock
    (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) :
    Measurable (physicalPencilFromExteriorNormalizedBlock p j V Γ e η) := by
  have hH := measurable_physicalMatrixFromExteriorNormalizedBlock p j
  rw [Matrix.measurable_iff]
  intro a b
  exact ((((Matrix.measurable_iff.mp hH a b).add measurable_const).sub
    measurable_const).add measurable_const)

/-- Evaluation on the exterior coordinates and normalized singleton block
recovers the raw physical absorbed pencil pointwise. -/
theorem Law.physicalPencilFromExteriorNormalizedBlock_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) (ω : M.Ω) :
    physicalPencilFromExteriorNormalizedBlock p j V Γ e η
      (M.exteriorUpperCoordinates j ω, M.normalizedSingletonBlock j ω) =
      M.H ω + V - (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
        Complex.I • (Γ + η • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)) := by
  rw [physicalPencilFromExteriorNormalizedBlock,
    M.physicalMatrixFromExteriorNormalizedBlock_coordinates j ω]

/-- The explicit `fromBlocks` decomposition of the reconstructed physical pencil in
the singleton/complement ordering. -/
theorem physicalPencil_submatrix_singletonPhysicalSplitEquiv
    (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ)
    (z : (exteriorUpperPairs p j → ℂ) ×
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ) :
    (physicalPencilFromExteriorNormalizedBlock p j V Γ e η z).submatrix
        (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j) =
      Matrix.fromBlocks
        ((physicalPencilFromExteriorNormalizedBlock p j V Γ e η z).submatrix
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a))
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a)))
        ((physicalPencilFromExteriorNormalizedBlock p j V Γ e η z).submatrix
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a))
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inr a)))
        ((physicalPencilFromExteriorNormalizedBlock p j V Γ e η z).submatrix
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inr a))
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a)))
        ((physicalPencilFromExteriorNormalizedBlock p j V Γ e η z).submatrix
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inr a))
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inr a))) := by
  ext (a | a) (b | b) <;> rfl

end GaussianRing
end CoareaNative.BlockBand
