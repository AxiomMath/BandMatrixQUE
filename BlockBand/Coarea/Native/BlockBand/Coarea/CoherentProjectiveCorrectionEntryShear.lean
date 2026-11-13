module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionTriangular
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionDeterminant
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Entry shears for the coherent projective correction

This module puts the arbitrary-coordinate correction into the selected
energy/projective/complement coordinates and exposes all nine of its blocks.
It also supplies the determinant-one elementary shears needed to remove
individual off-diagonal entries without changing the determinant.  Thus the
comparison with `coherentProjectiveCorrectionDiagonalModel` reduces to a
block-entry calculation on the explicit Householder product rule.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

/-- The global correction transported to selected
energy/projective/complement coordinates. -/
def coherentProjectiveCorrectionSelectedBlocks {d : ℕ} (i : Fin d)
    (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (coherentSelectedBlockCoordinateLinearEquiv i).toLinearMap.comp
    ((coherentEigenpairProjectiveCorrection i E z B hgap).comp
      (coherentSelectedBlockCoordinateLinearEquiv i).symm.toLinearMap)

/-- Selected-coordinate transport does not change the determinant of the
projective correction. -/
theorem det_coherentProjectiveCorrectionSelectedBlocks {d : ℕ} (i : Fin d)
    (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    LinearMap.det
      (coherentProjectiveCorrectionSelectedBlocks i E z B hgap) =
    LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap) := by
  exact LinearMap.det_conj
    (coherentEigenpairProjectiveCorrection i E z B hgap)
    (coherentSelectedBlockCoordinateLinearEquiv i)

section BlockCoordinates

variable {n : ℕ}

/-- Inclusion of the energy coordinate into the selected block carrier. -/
def eigenpairEnergyBlockInclusion :
    ℝ →ₗ[ℝ] EigenpairHermitianBlockCoordinates (Fin n) where
  toFun t := (t, (0, 0))
  map_add' x y := by
    ext <;> simp
  map_smul' c t := by
    ext <;> simp

/-- Inclusion of the affine projective coordinate into the selected carrier. -/
def eigenpairProjectiveBlockInclusion :
    (Fin n → ℂ) →ₗ[ℝ] EigenpairHermitianBlockCoordinates (Fin n) where
  toFun u := (0, (u, 0))
  map_add' x y := by
    ext <;> simp
  map_smul' c u := by
    ext <;> simp

/-- Inclusion of the complementary Hermitian coordinate block. -/
def eigenpairComplementBlockInclusion :
    RealHermitianMatrix (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n) where
  toFun C := (0, (0, C))
  map_add' x y := by
    ext <;> simp
  map_smul' c C := by
    ext <;> simp

/-- Energy projection from selected block coordinates. -/
def eigenpairEnergyBlockProjection :
    EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ((Fin n → ℂ) × RealHermitianMatrix (Fin n))

/-- Projective projection from selected block coordinates. -/
def eigenpairProjectiveBlockProjection :
    EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ] (Fin n → ℂ) :=
  (LinearMap.fst ℝ (Fin n → ℂ) (RealHermitianMatrix (Fin n))).comp
    (LinearMap.snd ℝ ℝ ((Fin n → ℂ) × RealHermitianMatrix (Fin n)))

/-- Complement projection from selected block coordinates. -/
def eigenpairComplementBlockProjection :
    EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      RealHermitianMatrix (Fin n) :=
  (LinearMap.snd ℝ (Fin n → ℂ) (RealHermitianMatrix (Fin n))).comp
    (LinearMap.snd ℝ ℝ ((Fin n → ℂ) × RealHermitianMatrix (Fin n)))

@[simp] theorem eigenpair_block_inclusions_sum
    (ξ : EigenpairHermitianBlockCoordinates (Fin n)) :
    eigenpairEnergyBlockInclusion (eigenpairEnergyBlockProjection ξ) +
      eigenpairProjectiveBlockInclusion
        (eigenpairProjectiveBlockProjection ξ) +
      eigenpairComplementBlockInclusion
        (eigenpairComplementBlockProjection ξ) = ξ := by
  rcases ξ with ⟨t, u, C⟩
  ext <;> simp [eigenpairEnergyBlockInclusion,
    eigenpairProjectiveBlockInclusion, eigenpairComplementBlockInclusion,
    eigenpairEnergyBlockProjection, eigenpairProjectiveBlockProjection,
    eigenpairComplementBlockProjection]

/-- Energy-to-energy block of an endomorphism in selected coordinates. -/
def eigenpairCorrectionEnergyEnergyBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) : ℝ →ₗ[ℝ] ℝ :=
  eigenpairEnergyBlockProjection.comp (L.comp eigenpairEnergyBlockInclusion)

/-- Projective-to-energy off-diagonal block. -/
def eigenpairCorrectionEnergyProjectiveBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  eigenpairEnergyBlockProjection.comp
    (L.comp eigenpairProjectiveBlockInclusion)

/-- Complement-to-energy off-diagonal block. -/
def eigenpairCorrectionEnergyComplementBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    RealHermitianMatrix (Fin n) →ₗ[ℝ] ℝ :=
  eigenpairEnergyBlockProjection.comp
    (L.comp eigenpairComplementBlockInclusion)

/-- Energy-to-projective off-diagonal block. -/
def eigenpairCorrectionProjectiveEnergyBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    ℝ →ₗ[ℝ] (Fin n → ℂ) :=
  eigenpairProjectiveBlockProjection.comp
    (L.comp eigenpairEnergyBlockInclusion)

/-- Projective diagonal block. -/
def eigenpairCorrectionProjectiveProjectiveBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
  eigenpairProjectiveBlockProjection.comp
    (L.comp eigenpairProjectiveBlockInclusion)

/-- Complement-to-projective off-diagonal block. -/
def eigenpairCorrectionProjectiveComplementBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    RealHermitianMatrix (Fin n) →ₗ[ℝ] (Fin n → ℂ) :=
  eigenpairProjectiveBlockProjection.comp
    (L.comp eigenpairComplementBlockInclusion)

/-- Energy-to-complement off-diagonal block. -/
def eigenpairCorrectionComplementEnergyBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    ℝ →ₗ[ℝ] RealHermitianMatrix (Fin n) :=
  eigenpairComplementBlockProjection.comp
    (L.comp eigenpairEnergyBlockInclusion)

/-- Projective-to-complement off-diagonal block. -/
def eigenpairCorrectionComplementProjectiveBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    (Fin n → ℂ) →ₗ[ℝ] RealHermitianMatrix (Fin n) :=
  eigenpairComplementBlockProjection.comp
    (L.comp eigenpairProjectiveBlockInclusion)

/-- Complement diagonal block. -/
def eigenpairCorrectionComplementComplementBlock
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n)) :
    RealHermitianMatrix (Fin n) →ₗ[ℝ] RealHermitianMatrix (Fin n) :=
  eigenpairComplementBlockProjection.comp
    (L.comp eigenpairComplementBlockInclusion)

/-- Exact reconstruction of an endomorphism from its three block rows.  This
turns equality with the diagonal model into nine entrywise goals. -/
theorem eigenpairCorrection_apply_eq_block_rows
    (L : EigenpairHermitianBlockCoordinates (Fin n) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin n))
    (ξ : EigenpairHermitianBlockCoordinates (Fin n)) :
    L ξ =
      eigenpairEnergyBlockInclusion
        (eigenpairEnergyBlockProjection (L ξ)) +
      eigenpairProjectiveBlockInclusion
        (eigenpairProjectiveBlockProjection (L ξ)) +
      eigenpairComplementBlockInclusion
        (eigenpairComplementBlockProjection (L ξ)) := by
  symm
  exact eigenpair_block_inclusions_sum (L ξ)

/-- The diagonal model has identity energy block. -/
@[simp] theorem diagonalModel_energyEnergyBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionEnergyEnergyBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = LinearMap.id := by
  apply LinearMap.ext
  intro t
  simp [eigenpairCorrectionEnergyEnergyBlock,
    eigenpairEnergyBlockProjection, eigenpairEnergyBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal model has the normalized affine tangent as its projective
block. -/
@[simp] theorem diagonalModel_projectiveProjectiveBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionProjectiveProjectiveBlock
      (coherentProjectiveCorrectionBlockDiagonal z) =
        projectiveNormalizedTangentBlock z := by
  apply LinearMap.ext
  intro u
  simp [eigenpairCorrectionProjectiveProjectiveBlock,
    eigenpairProjectiveBlockProjection, eigenpairProjectiveBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal model has identity complementary block. -/
@[simp] theorem diagonalModel_complementComplementBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionComplementComplementBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = LinearMap.id := by
  apply LinearMap.ext
  intro C
  simp [eigenpairCorrectionComplementComplementBlock,
    eigenpairComplementBlockProjection, eigenpairComplementBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no projective-to-energy entry. -/
@[simp] theorem diagonalModel_energyProjectiveBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionEnergyProjectiveBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext u
  simp [eigenpairCorrectionEnergyProjectiveBlock,
    eigenpairEnergyBlockProjection, eigenpairProjectiveBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no complement-to-energy entry. -/
@[simp] theorem diagonalModel_energyComplementBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionEnergyComplementBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext C
  simp [eigenpairCorrectionEnergyComplementBlock,
    eigenpairEnergyBlockProjection, eigenpairComplementBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no energy-to-projective entry. -/
@[simp] theorem diagonalModel_projectiveEnergyBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionProjectiveEnergyBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext t
  simp [eigenpairCorrectionProjectiveEnergyBlock,
    eigenpairProjectiveBlockProjection, eigenpairEnergyBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no complement-to-projective entry. -/
@[simp] theorem diagonalModel_projectiveComplementBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionProjectiveComplementBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext C j
  simp [eigenpairCorrectionProjectiveComplementBlock,
    eigenpairProjectiveBlockProjection, eigenpairComplementBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no energy-to-complement entry. -/
@[simp] theorem diagonalModel_complementEnergyBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionComplementEnergyBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext t j
  simp [eigenpairCorrectionComplementEnergyBlock,
    eigenpairComplementBlockProjection, eigenpairEnergyBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

/-- The diagonal comparison model has no projective-to-complement entry. -/
@[simp] theorem diagonalModel_complementProjectiveBlock {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    eigenpairCorrectionComplementProjectiveBlock
      (coherentProjectiveCorrectionBlockDiagonal z) = 0 := by
  ext u j k
  simp [eigenpairCorrectionComplementProjectiveBlock,
    eigenpairComplementBlockProjection, eigenpairProjectiveBlockInclusion,
    coherentProjectiveCorrectionBlockDiagonal]

end BlockCoordinates

section EntryShears

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
  [Module.Free ℝ X] [Module.Finite ℝ X]

/-- An elementary entry shear `u ↦ u + f(u) v`.  The side condition used
below says the modified output entry is different from the input entry read by
`f`, exactly as for an off-diagonal elementary matrix. -/
def coherentProjectiveCorrectionEntryShear
    (f : Module.Dual ℝ X) (v : X) : X →ₗ[ℝ] X :=
  LinearMap.transvection f v

@[simp] theorem coherentProjectiveCorrectionEntryShear_apply
    (f : Module.Dual ℝ X) (v u : X) :
    coherentProjectiveCorrectionEntryShear f v u = u + f u • v := by
  rfl

/-- Every off-diagonal entry shear has determinant one. -/
theorem det_coherentProjectiveCorrectionEntryShear
    (f : Module.Dual ℝ X) (v : X) (hoff : f v = 0) :
    LinearMap.det (coherentProjectiveCorrectionEntryShear f v) = 1 := by
  rw [coherentProjectiveCorrectionEntryShear, LinearMap.transvection.det,
    hoff, add_zero]

/-- Removing one off-diagonal entry shear preserves a preceding determinant. -/
theorem det_comp_coherentProjectiveCorrectionEntryShear
    (L : X →ₗ[ℝ] X) (f : Module.Dual ℝ X) (v : X)
    (hoff : f v = 0) :
    LinearMap.det
      (L.comp (coherentProjectiveCorrectionEntryShear f v)) =
        LinearMap.det L := by
  rw [LinearMap.det_comp,
    det_coherentProjectiveCorrectionEntryShear f v hoff, mul_one]

/-- The same determinant invariance holds when the shear is applied on the
output side. -/
theorem det_coherentProjectiveCorrectionEntryShear_comp
    (L : X →ₗ[ℝ] X) (f : Module.Dual ℝ X) (v : X)
    (hoff : f v = 0) :
    LinearMap.det
      ((coherentProjectiveCorrectionEntryShear f v).comp L) =
        LinearMap.det L := by
  rw [LinearMap.det_comp,
    det_coherentProjectiveCorrectionEntryShear f v hoff, one_mul]

/-- A finite product of elementary entry shears.  The order is the matrix
elimination order: the head shear acts last on a vector. -/
def coherentProjectiveCorrectionEntryShearProduct :
    List (Module.Dual ℝ X × X) → (X →ₗ[ℝ] X)
  | [] => LinearMap.id
  | (f, v) :: S =>
      (coherentProjectiveCorrectionEntryShear f v).comp
        (coherentProjectiveCorrectionEntryShearProduct S)

@[simp] theorem det_coherentProjectiveCorrectionEntryShearProduct
    (S : List (Module.Dual ℝ X × X))
    (hoff : ∀ p ∈ S, p.1 p.2 = 0) :
    LinearMap.det (coherentProjectiveCorrectionEntryShearProduct S) = 1 := by
  induction S with
  | nil =>
      simp [coherentProjectiveCorrectionEntryShearProduct]
  | cons p S ih =>
      rw [coherentProjectiveCorrectionEntryShearProduct, LinearMap.det_comp,
        det_coherentProjectiveCorrectionEntryShear p.1 p.2
          (hoff p (by simp)), ih (fun q hq => hoff q (by simp [hq])),
        one_mul]

/-- A complete finite elimination by off-diagonal entry shears
preserves the determinant of the map being reduced. -/
theorem det_comp_coherentProjectiveCorrectionEntryShearProduct
    (L : X →ₗ[ℝ] X) (S : List (Module.Dual ℝ X × X))
    (hoff : ∀ p ∈ S, p.1 p.2 = 0) :
    LinearMap.det
      (L.comp (coherentProjectiveCorrectionEntryShearProduct S)) =
        LinearMap.det L := by
  rw [LinearMap.det_comp,
    det_coherentProjectiveCorrectionEntryShearProduct S hoff, mul_one]

/-- Output-side finite entry elimination likewise preserves determinant. -/
theorem det_coherentProjectiveCorrectionEntryShearProduct_comp
    (L : X →ₗ[ℝ] X) (S : List (Module.Dual ℝ X × X))
    (hoff : ∀ p ∈ S, p.1 p.2 = 0) :
    LinearMap.det
      ((coherentProjectiveCorrectionEntryShearProduct S).comp L) =
        LinearMap.det L := by
  rw [LinearMap.det_comp,
    det_coherentProjectiveCorrectionEntryShearProduct S hoff, one_mul]

end EntryShears

end CoareaNative.BlockBand
