module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGaussianSplit
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurCoareaData

/-!
# Deterministic Schur readback for the adjacent pair

This module reads the concrete exterior/coupling state produced by
`actualPairExteriorCouplingState` into the `H_R`, `C`, and `V` arguments of the
physical Schur-coarea formulas.  The finite reindexings are fixed explicitly:
the exterior is sent to `Fin card`, while the retained `Fin (2W)` pair is sent
to the selected-first index `Unit ⊕ Fin (2W-1)`.

It also proves the deterministic residual translation.  Replacing residual
coordinates `z` by the total exposed block `z+g` adds exactly the reindexed
fresh block to `V`, hence to `F(E)`, while `T(E)` and `𝒟(E)` are unchanged.
No probabilistic identification is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix Set
open scoped ComplexOrder

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Exterior dimension of the adjacent-pair split. -/
abbrev ActualPairExteriorDimension (p : Params) (j : ZMod p.n) :=
  Fintype.card (AdjacentPairExteriorIndex p j)

/-- Canonical finite numbering of the pair exterior. -/
def actualPairExteriorEquivFin (p : Params) (j : ZMod p.n) :
    AdjacentPairExteriorIndex p j ≃ Fin (ActualPairExteriorDimension p j) :=
  Fintype.equivFin _

/-- A distinguished retained coordinate; positivity follows from `W ≥ 1`. -/
def actualPairFirstCoordinate (p : Params) : Fin (2 * p.W) :=
  ⟨0, by nlinarith [p.W_pos]⟩

/-- Selected-first reindexing of the adjacent pair used by physical coarea. -/
def actualPairSelectedEquiv (p : Params) :
    Fin (2 * p.W) ≃ Unit ⊕ Fin (2 * p.W - 1) :=
  selectedCoordinateEquiv (actualPairFirstCoordinate p)

/-- Exterior Hermitian matrix `H_R`, reindexed to `Fin card`. -/
def actualPairStateHR (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) :
    Matrix (Fin (ActualPairExteriorDimension p j))
      (Fin (ActualPairExteriorDimension p j)) ℂ :=
  Matrix.reindex (actualPairExteriorEquivFin p j)
    (actualPairExteriorEquivFin p j) ξ.1.1

/-- Exterior-to-pair coupling `C`, in selected-first retained coordinates. -/
def actualPairStateC (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) :
    Matrix (Fin (ActualPairExteriorDimension p j))
      (Unit ⊕ Fin (2 * p.W - 1)) ℂ :=
  Matrix.reindex (actualPairExteriorEquivFin p j)
    (actualPairSelectedEquiv p) ξ.2

/-- A retained Hermitian coordinate vector read as the physical deterministic
compression `V` in selected-first coordinates. -/
def actualPairStateV (p : Params)
    (z : HermitianCoordinateSpace (2 * p.W)) :
    Matrix (Unit ⊕ Fin (2 * p.W - 1))
      (Unit ⊕ Fin (2 * p.W - 1)) ℂ :=
  Matrix.reindex (actualPairSelectedEquiv p)
    (actualPairSelectedEquiv p) (hermitianOfFinCoordinates (2 * p.W) z).1

/-- Block reconstruction from retained coordinates and the unchanged
exterior/coupling state. -/
def actualPairBlockReconstruction (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    Matrix ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j))
      ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) ℂ :=
  Matrix.fromBlocks (actualPairStateV p z) (actualPairStateC p j ξ)ᴴ
    (actualPairStateC p j ξ) (actualPairStateHR p j ξ)

/-- The exterior readback remains Hermitian. -/
theorem actualPairStateHR_isHermitian (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) :
    (actualPairStateHR p j ξ).IsHermitian := by
  simpa [actualPairStateHR] using
    ξ.1.2.reindex (actualPairExteriorEquivFin p j)

/-- The retained readback remains Hermitian. -/
theorem actualPairStateV_isHermitian (p : Params)
    (z : HermitianCoordinateSpace (2 * p.W)) :
    (actualPairStateV p z).IsHermitian := by
  simpa [actualPairStateV] using
    (hermitianOfFinCoordinates (2 * p.W) z).2.reindex (actualPairSelectedEquiv p)

/-- The block reconstruction is Hermitian. -/
theorem actualPairBlockReconstruction_isHermitian
    (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    (actualPairBlockReconstruction p j z ξ).IsHermitian := by
  apply Matrix.isHermitian_fromBlocks_iff.mpr
  exact ⟨actualPairStateV_isHermitian p z,
    Matrix.conjTranspose_conjTranspose _, rfl, actualPairStateHR_isHermitian p j ξ⟩

/-- The sampled adjacent pair reads back to its original matrix. -/
theorem actualPairStateV_actualAdjacentPairCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    actualPairStateV p (M.actualAdjacentPairCoordinates j ω) =
      Matrix.reindex (actualPairSelectedEquiv p)
        (actualPairSelectedEquiv p) (M.actualAdjacentPairMatrix j ω).1 := by
  unfold actualPairStateV Law.actualAdjacentPairCoordinates
  have h := (hermitianFinCoordinatesLinearEquiv (2 * p.W)).apply_symm_apply
    (M.actualAdjacentPairMatrix j ω)
  exact congrArg (fun A : HermitianMatrix (Fin (2 * p.W)) =>
    Matrix.reindex (actualPairSelectedEquiv p) (actualPairSelectedEquiv p) A.1) h

/-- The three pieces of the state reconstruct the full matrix in
pair/exterior block order. -/
theorem actualPairBlockReconstruction_actual
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    actualPairBlockReconstruction p j (M.actualAdjacentPairCoordinates j ω)
      (M.actualPairExteriorCouplingState j ω) =
    Matrix.fromBlocks
      (Matrix.reindex (actualPairSelectedEquiv p)
        (actualPairSelectedEquiv p) (M.actualAdjacentPairMatrix j ω).1)
      (actualPairStateC p j (M.actualPairExteriorCouplingState j ω))ᴴ
      (actualPairStateC p j (M.actualPairExteriorCouplingState j ω))
      (actualPairStateHR p j (M.actualPairExteriorCouplingState j ω)) := by
  rw [actualPairBlockReconstruction,
    actualPairStateV_actualAdjacentPairCoordinates]

/-- The deterministic site readback: retained selected-first coordinates
are followed by the canonically numbered physical exterior. -/
def actualPairReadbackSite (p : Params) (j : ZMod p.n) :
    ((Unit ⊕ Fin (2 * p.W - 1)) ⊕ Fin (ActualPairExteriorDimension p j)) →
      Site p.n p.W
  | Sum.inl a => adjacentPairSite p j ((actualPairSelectedEquiv p).symm a)
  | Sum.inr k => ((actualPairExteriorEquivFin p j).symm k).1

/-- Readback of the sampled pair and its exterior/coupling state is
entrywise the original physical Hamiltonian, in deterministic pair/exterior
order.  This is the full block-matrix identity, not merely extraction of its
three constituent blocks. -/
theorem actualPairBlockReconstruction_eq_full_submatrix
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    actualPairBlockReconstruction p j (M.actualAdjacentPairCoordinates j ω)
        (M.actualPairExteriorCouplingState j ω) =
      (M.H ω).submatrix (actualPairReadbackSite p j)
        (actualPairReadbackSite p j) := by
  rw [actualPairBlockReconstruction_actual]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · change star ((M.H ω) _ _) = (M.H ω) _ _
    have h := congrFun (congrFun (M.H_hermitian ω)
      (adjacentPairSite p j ((actualPairSelectedEquiv p).symm a)))
      ((actualPairExteriorEquivFin p j).symm b).1
    simpa [Matrix.conjTranspose_apply, actualPairReadbackSite] using h
  · rfl
  · rfl

/-- Coordinate reconstruction is additive before the fixed reindexing. -/
theorem actualPairStateV_add (p : Params)
    (z g : HermitianCoordinateSpace (2 * p.W)) :
    actualPairStateV p (z + g) = actualPairStateV p z + actualPairStateV p g := by
  unfold actualPairStateV
  rw [show (hermitianOfFinCoordinates (2 * p.W) (z + g)).1 =
      (hermitianOfFinCoordinates (2 * p.W) z).1 +
        (hermitianOfFinCoordinates (2 * p.W) g).1 by
    exact congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv
      (2 * p.W)).map_add z g)]
  ext a b
  rfl

/-- Deterministic residual translation of the whole block matrix: only the
retained block changes. -/
theorem actualPairBlockReconstruction_add
    (p : Params) (j : ZMod p.n)
    (z g : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    actualPairBlockReconstruction p j (z + g) ξ =
      actualPairBlockReconstruction p j z ξ +
        Matrix.fromBlocks (actualPairStateV p g) 0 0 0 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [actualPairBlockReconstruction, actualPairStateV_add]

/-- Physical Schur compression read from the exterior state and a
retained residual block. -/
def actualPairPhysicalCoareaF (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ) :=
  physicalCoareaF (actualPairStateHR p j ξ) (actualPairStateC p j ξ)
    (actualPairStateV p z) E

/-- Physical transfer read from the exterior state. -/
def actualPairPhysicalCoareaT (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :=
  physicalCoareaT (actualPairStateHR p j ξ) (actualPairStateC p j ξ) E

/-- Physical positive clock read from the exterior state. -/
def actualPairPhysicalCoareaD (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :=
  physicalCoareaD (actualPairStateHR p j ξ) (actualPairStateC p j ξ) E

/-- Residual translation passes through the physical Schur compression. -/
theorem actualPairPhysicalCoareaF_add
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z g : HermitianCoordinateSpace (2 * p.W)) (E : ℝ) :
    actualPairPhysicalCoareaF p j ξ (z + g) E =
      actualPairPhysicalCoareaF p j ξ z E + actualPairStateV p g := by
  unfold actualPairPhysicalCoareaF physicalCoareaF
  rw [actualPairStateV_add]
  abel

/-- The transfer is independent of residual translation. -/
theorem actualPairPhysicalCoareaT_readback
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :
    actualPairPhysicalCoareaT p j ξ E =
      physicalCoareaT (actualPairStateHR p j ξ) (actualPairStateC p j ξ) E := rfl

/-- The positive clock is independent of residual translation. -/
theorem actualPairPhysicalCoareaD_readback
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :
    actualPairPhysicalCoareaD p j ξ E =
      physicalCoareaD (actualPairStateHR p j ξ) (actualPairStateC p j ξ) E := rfl

/-- The read-back clock is positive definite. -/
theorem actualPairPhysicalCoareaD_posDef
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :
    (actualPairPhysicalCoareaD p j ξ E).PosDef :=
  physicalCoareaD_posDef _ _ _

/-- Projective scalar compression for the state. -/
def actualPairPhysicalCoarea_f (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) : ℝ :=
  physicalCoarea_f (actualPairStateHR p j ξ) (actualPairStateC p j ξ)
    (actualPairStateV p z) E u

/-- Projective perpendicular column for the state. -/
def actualPairPhysicalCoarea_q (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) : Fin (2 * p.W - 1) → ℂ :=
  physicalCoarea_q (actualPairStateHR p j ξ) (actualPairStateC p j ξ)
    (actualPairStateV p z) E u

/-- Projective complementary compression for the state. -/
def actualPairPhysicalCoareaFv (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) :
    Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ :=
  physicalCoareaFv (actualPairStateHR p j ξ) (actualPairStateC p j ξ)
    (actualPairStateV p z) E u

/-- The read-back `F_v` is Hermitian. -/
theorem actualPairPhysicalCoareaFv_isHermitian
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) :
    (actualPairPhysicalCoareaFv p j ξ z E u).IsHermitian :=
  physicalCoareaFv_isHermitian _ _ _
    (actualPairStateHR_isHermitian p j ξ) (actualPairStateV_isHermitian p z) E u

/-- The paper's reconstruction `L_E v = (v,-T(E)v)` for the
concrete pair/exterior state.  It uses the globally totalized physical
resolvent; on the pole-free set this is the ordinary Schur reconstruction. -/
def actualPairPhysicalSchurReconstruction
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ)
    (v : (Unit ⊕ Fin (2 * p.W - 1)) → ℂ) :
    ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) → ℂ :=
  v ⊕ᵥ (-(actualPairPhysicalCoareaT p j ξ E *ᵥ v))

/-- At a pole-free energy, an eigenvector of the concrete Schur
compression reconstructs to an eigenvector of the complete deterministic
pair/exterior block matrix.  Thus the vector used by the paper's endpoint
is a selected full-matrix eigenvector, rather than only a retained
coordinate. -/
theorem actualPairSchurReconstruction_eigenvector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (v : (Unit ⊕ Fin (2 * p.W - 1)) → ℂ)
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    (hv : actualPairPhysicalCoareaF p j ξ z E *ᵥ v = (E : ℂ) • v) :
    actualPairBlockReconstruction p j z ξ *ᵥ
        actualPairPhysicalSchurReconstruction p j ξ E v =
      (E : ℂ) • actualPairPhysicalSchurReconstruction p j ξ E v := by
  let _ : Invertible
      (physicalExteriorPencil (actualPairStateHR p j ξ) E) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hpole)
  have hschur :
      physicalSchurMatrix (actualPairStateV p z)
          (actualPairStateC p j ξ)ᴴ (actualPairStateHR p j ξ) E *ᵥ v = 0 := by
    rw [← physicalCoareaF_sub_energy_eq_physicalSchurMatrix]
    rw [Matrix.sub_mulVec]
    change actualPairPhysicalCoareaF p j ξ z E *ᵥ v - _ = 0
    rw [hv, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_self _
  have hkernel := physicalBlockPencil_mulVec_schurReconstruction
    (actualPairStateV p z) (actualPairStateC p j ξ)ᴴ
    (actualPairStateHR p j ξ) E v
  rw [hschur] at hkernel
  simp only [Matrix.conjTranspose_conjTranspose] at hkernel
  simp at hkernel
  have hreconstruction :
      schurReconstruction (actualPairStateC p j ξ)
          (physicalExteriorPencil (actualPairStateHR p j ξ) E) v =
        actualPairPhysicalSchurReconstruction p j ξ E v := by
    unfold schurReconstruction schurTransfer
      actualPairPhysicalSchurReconstruction actualPairPhysicalCoareaT
      physicalCoareaT physicalCoareaResolvent
    change v ⊕ᵥ (-((⅟(physicalExteriorPencil
      (actualPairStateHR p j ξ) E) * actualPairStateC p j ξ) *ᵥ v)) =
      v ⊕ᵥ (-(((physicalExteriorPencil
        (actualPairStateHR p j ξ) E)⁻¹ * actualPairStateC p j ξ) *ᵥ v))
    rw [Matrix.invOf_eq_nonsing_inv]
  rw [hreconstruction] at hkernel
  have hpencil :
      physicalBlockPencil (actualPairStateV p z)
          (actualPairStateC p j ξ)ᴴ (actualPairStateHR p j ξ) E =
        actualPairBlockReconstruction p j z ξ - (E : ℂ) • 1 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [physicalBlockPencil, physicalRetainedPencil, physicalExteriorPencil,
        actualPairBlockReconstruction, Matrix.one_apply]
  rw [hpencil, Matrix.sub_mulVec] at hkernel
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hkernel
  exact sub_eq_zero.mp hkernel

/-- In particular, the phase-fixed affine representative used by
`physicalCoarea_f`, `q`, and `F_v` reconstructs to the full physical
pair/exterior eigenvector whenever its Schur equation holds. -/
theorem actualPairCanonicalSchurReconstruction_eigenvector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ)
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    (hv : actualPairPhysicalCoareaF p j ξ z E *ᵥ
        canonicalProjectiveUnitVector u =
      (E : ℂ) • canonicalProjectiveUnitVector u) :
    actualPairBlockReconstruction p j z ξ *ᵥ
        actualPairPhysicalSchurReconstruction p j ξ E
          (canonicalProjectiveUnitVector u) =
      (E : ℂ) • actualPairPhysicalSchurReconstruction p j ξ E
        (canonicalProjectiveUnitVector u) :=
  actualPairSchurReconstruction_eigenvector p j ξ z E
    (canonicalProjectiveUnitVector u) hpole hv

/-- The normalized full Schur eigenvector `ψ=L_Ev/‖L_Ev‖` appearing
in the paper's endpoint, specialized to the phase-fixed affine direction. -/
def actualPairNormalizedSchurEigenvector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) :
    ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) → ℂ :=
  let w := actualPairPhysicalSchurReconstruction p j ξ E
    (canonicalProjectiveUnitVector u)
  ((‖w‖⁻¹ : ℝ) : ℂ) • w

/-- The unnormalized Schur reconstruction of the canonical projective vector
is nonzero because its retained component is the unit vector itself. -/
theorem actualPairCanonicalSchurReconstruction_ne_zero
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) :
    actualPairPhysicalSchurReconstruction p j ξ E
      (canonicalProjectiveUnitVector u) ≠ 0 := by
  intro hzero
  have hvzero : canonicalProjectiveUnitVector u = 0 := by
    ext i
    exact congrFun hzero (Sum.inl i)
  have hnorm := norm_canonicalProjectiveUnitVector u
  rw [hvzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The read-back vector `ψ` has unit norm. -/
theorem norm_actualPairNormalizedSchurEigenvector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ) :
    ‖actualPairNormalizedSchurEigenvector p j ξ E u‖ = 1 := by
  unfold actualPairNormalizedSchurEigenvector
  rw [norm_smul]
  simp [actualPairCanonicalSchurReconstruction_ne_zero p j ξ E u]

/-- Normalization preserves the full block-matrix eigenvector equation. -/
theorem actualPairNormalizedSchurEigenvector_eigenvector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ)
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    (hv : actualPairPhysicalCoareaF p j ξ z E *ᵥ
        canonicalProjectiveUnitVector u =
      (E : ℂ) • canonicalProjectiveUnitVector u) :
    actualPairBlockReconstruction p j z ξ *ᵥ
        actualPairNormalizedSchurEigenvector p j ξ E u =
      (E : ℂ) • actualPairNormalizedSchurEigenvector p j ξ E u := by
  unfold actualPairNormalizedSchurEigenvector
  rw [Matrix.mulVec_smul,
    actualPairCanonicalSchurReconstruction_eigenvector p j ξ z E u hpole hv]
  rw [smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- For the sampled exterior state and sampled adjacent block, the
normalized Schur vector is an eigenvector of the original physical Hamiltonian
read in the deterministic pair/exterior order. -/
theorem Law.actualPairNormalizedSchurEigenvector_fullPhysical
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) (E : ℝ)
    (u : Fin (2 * p.W - 1) → ℂ)
    (hpole : E ∈ physicalCoareaPoleFreeSet
      (actualPairStateHR p j (M.actualPairExteriorCouplingState j ω)))
    (hv : actualPairPhysicalCoareaF p j
        (M.actualPairExteriorCouplingState j ω)
        (M.actualAdjacentPairCoordinates j ω) E *ᵥ
          canonicalProjectiveUnitVector u =
      (E : ℂ) • canonicalProjectiveUnitVector u) :
    (M.H ω).submatrix (actualPairReadbackSite p j)
          (actualPairReadbackSite p j) *ᵥ
        actualPairNormalizedSchurEigenvector p j
          (M.actualPairExteriorCouplingState j ω) E u =
      (E : ℂ) • actualPairNormalizedSchurEigenvector p j
        (M.actualPairExteriorCouplingState j ω) E u := by
  rw [← actualPairBlockReconstruction_eq_full_submatrix M j ω]
  exact actualPairNormalizedSchurEigenvector_eigenvector p j
    (M.actualPairExteriorCouplingState j ω)
    (M.actualAdjacentPairCoordinates j ω) E u hpole hv

/-- Exterior inertia gives the exact ordered-rank alignment of a pole-free
full eigenvalue with its retained Schur crossing.  This is the
specialization of the static inertia identity to the adjacent pair. -/
theorem actualPairPhysicalOrderedRank_iff_additiveSchurSector
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W)) (E : ℝ)
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    (α : Fin (Fintype.card
      ((Unit ⊕ Fin (2 * p.W - 1)) ⊕ Fin (ActualPairExteriorDimension p j)))) :
    orderedZeroRank
        (physicalBlockHermitian (actualPairStateV p z)
          (actualPairStateC p j ξ)ᴴ (actualPairStateHR p j ξ)
          (actualPairStateV_isHermitian p z)
          (actualPairStateHR_isHermitian p j ξ) E).property = α.val + 1 ↔
      negativeEigenvalueCount
          (physicalExteriorFamily (actualPairStateHR p j ξ)
            (actualPairStateHR_isHermitian p j ξ) E).property +
        negativeEigenvalueCount
          (physicalSchurFamily (actualPairStateV p z)
            (actualPairStateC p j ξ)ᴴ (actualPairStateHR p j ξ)
            (actualPairStateV_isHermitian p z)
            (actualPairStateHR_isHermitian p j ξ) E).property + 1 =
          α.val + 1 := by
  let _ : Invertible
      (physicalExteriorPencil (actualPairStateHR p j ξ) E) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hpole)
  exact physicalOrderedRank_iff_additiveSchurSector
    (actualPairStateV p z) (actualPairStateC p j ξ)ᴴ
    (actualPairStateHR p j ξ) (actualPairStateV_isHermitian p z)
    (actualPairStateHR_isHermitian p j ξ) E α

/-- Fully specialized physical Schur density, with explicit exterior data. -/
def actualPairPhysicalSchurCoareaDensity
    (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j)
    (z : HermitianCoordinateSpace (2 * p.W))
    (α : ℕ) (R : HermitianCoordinateSpace (ActualPairExteriorDimension p j))
    (i : Fin (2 * p.W)) (t : ℝ) (x : HermitianCoordinateSpace (2 * p.W)) : ENNReal :=
  physicalSchurCoareaDensity α R i t
    (actualPairStateHR p j ξ) (actualPairStateC p j ξ)
    (actualPairStateV p z) x

end GaussianRing
end CoareaNative.BlockBand
