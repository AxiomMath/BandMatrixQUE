module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HouseholderEigenpairSmoothCompletion
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairJacobianLocal

/-!
# Hermitian eigenpair block coordinates

A Hermitian matrix relative to a distinguished unit vector splits into one real
energy coordinate, one complex off-diagonal/projective-tangent column, and a
Hermitian complementary block.  This module constructs that split on the
canonical index decomposition `Unit ⊕ n`, proves exact two-sided reconstruction,
and packages it as a real-linear equivalence.  Composing this equivalence with
the phase-fixed Householder conjugation provides the algebraic coordinate map
needed by each ordered eigenline chart.

The remaining nonlinear calculation for a complete coarea chart is precisely
the derivative of this composition when the Householder vector itself varies
with the projective coordinate.  The already proved canonical commutator theorem
identifies its off-diagonal derivative with `E I - B`; no claim about a global
chart is made here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Hermitian matrices as a real subspace of all complex matrices. -/
def hermitianMatrixRealSubmodule (n : Type*) :
    Submodule ℝ (Matrix n n ℂ) where
  carrier := {A | A.IsHermitian}
  zero_mem' := by simp [Matrix.IsHermitian]
  add_mem' hA hB := hA.add hB
  smul_mem' c A hA := by
    change ((c : ℂ) • A).IsHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.eq]
    simp

/-- The real vector space of complex Hermitian matrices. -/
abbrev RealHermitianMatrix (n : Type*) :=
  ↥(hermitianMatrixRealSubmodule n)

/-- Real eigenpair block coordinates: energy, complex tangent column, and
Hermitian complementary block. -/
abbrev EigenpairHermitianBlockCoordinates (n : Type*) [Fintype n]
    [DecidableEq n] :=
  ℝ × ((n → ℂ) × RealHermitianMatrix n)

/-- The lower-right principal block of a Hermitian matrix is Hermitian. -/
theorem isHermitian_submatrix_inr
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : RealHermitianMatrix (Unit ⊕ n)) :
    (A.1.submatrix Sum.inr Sum.inr).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  exact A.property.apply (Sum.inr i) (Sum.inr j)

/-- Extract energy, lower-left tangent column, and complementary block. -/
def encodeEigenpairHermitianBlocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : RealHermitianMatrix (Unit ⊕ n)) :
    EigenpairHermitianBlockCoordinates n :=
  ((A.1 (Sum.inl Unit.unit) (Sum.inl Unit.unit)).re,
    (fun i => A.1 (Sum.inr i) (Sum.inl Unit.unit),
      ⟨A.1.submatrix Sum.inr Sum.inr, isHermitian_submatrix_inr A⟩))

/-- Reconstruct a Hermitian matrix from energy, tangent column, and complement. -/
def decodeEigenpairHermitianBlocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (y : EigenpairHermitianBlockCoordinates n) :
    RealHermitianMatrix (Unit ⊕ n) :=
  ⟨Matrix.fromBlocks ((y.1 : ℂ) • (1 : Matrix Unit Unit ℂ))
      (eigenpairTangentColumn y.2.1)ᴴ
      (eigenpairTangentColumn y.2.1) y.2.2.1,
    Matrix.isHermitian_fromBlocks_iff.mpr
      ⟨by
        rw [Matrix.IsHermitian]
        ext i j
        simp,
       Matrix.conjTranspose_conjTranspose _, rfl, y.2.2.2⟩⟩

/-- Extracting coordinates after block reconstruction is the identity. -/
theorem encode_decodeEigenpairHermitianBlocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (y : EigenpairHermitianBlockCoordinates n) :
    encodeEigenpairHermitianBlocks (decodeEigenpairHermitianBlocks y) = y := by
  rcases y with ⟨E, z, B⟩
  ext <;> simp [encodeEigenpairHermitianBlocks,
    decodeEigenpairHermitianBlocks, eigenpairTangentColumn]

/-- Reconstructing from extracted blocks returns the original Hermitian matrix. -/
theorem decode_encodeEigenpairHermitianBlocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : RealHermitianMatrix (Unit ⊕ n)) :
    decodeEigenpairHermitianBlocks (encodeEigenpairHermitianBlocks A) = A := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [encodeEigenpairHermitianBlocks, decodeEigenpairHermitianBlocks]
      using A.property.coe_re_apply_self (Sum.inl i)
  · rw [← A.property.apply (Sum.inl i) (Sum.inr j)]
    simp [encodeEigenpairHermitianBlocks, decodeEigenpairHermitianBlocks,
      eigenpairTangentColumn]
  · simp [encodeEigenpairHermitianBlocks, decodeEigenpairHermitianBlocks,
      eigenpairTangentColumn]
  · simp [encodeEigenpairHermitianBlocks, decodeEigenpairHermitianBlocks]

/-- Exact real-coordinate equivalence for the Hermitian eigenpair block split. -/
def eigenpairHermitianBlockEquiv
    (n : Type*) [Fintype n] [DecidableEq n] :
    RealHermitianMatrix (Unit ⊕ n) ≃ EigenpairHermitianBlockCoordinates n where
  toFun := encodeEigenpairHermitianBlocks
  invFun := decodeEigenpairHermitianBlocks
  left_inv := decode_encodeEigenpairHermitianBlocks
  right_inv := encode_decodeEigenpairHermitianBlocks

/-- Reconstruction is additive. -/
theorem decodeEigenpairHermitianBlocks_add
    {n : Type*} [Fintype n] [DecidableEq n]
    (x y : EigenpairHermitianBlockCoordinates n) :
    decodeEigenpairHermitianBlocks (x + y) =
      decodeEigenpairHermitianBlocks x + decodeEigenpairHermitianBlocks y := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [decodeEigenpairHermitianBlocks, eigenpairTangentColumn]

/-- Reconstruction respects real scalar multiplication. -/
theorem decodeEigenpairHermitianBlocks_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (x : EigenpairHermitianBlockCoordinates n) :
    decodeEigenpairHermitianBlocks (c • x) =
      c • decodeEigenpairHermitianBlocks x := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [decodeEigenpairHermitianBlocks, eigenpairTangentColumn]

/-- The block split is a real-linear equivalence, giving the required exact
dimension bookkeeping without a separate cardinality calculation. -/
def eigenpairHermitianBlockLinearEquiv
    (n : Type*) [Fintype n] [DecidableEq n] :
    RealHermitianMatrix (Unit ⊕ n) ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates n :=
  { eigenpairHermitianBlockEquiv n with
    map_add' := by
      intro A B
      ext <;> simp [eigenpairHermitianBlockEquiv,
        encodeEigenpairHermitianBlocks]
    map_smul' := by
      intro c A
      ext <;> simp [eigenpairHermitianBlockEquiv,
        encodeEigenpairHermitianBlocks] }

/-- Dimension bookkeeping for the energy/tangent/complement split. -/
theorem finrank_realHermitian_sum_eq_blockCoordinates
    (n : Type*) [Fintype n] [DecidableEq n] :
    Module.finrank ℝ (RealHermitianMatrix (Unit ⊕ n)) =
      Module.finrank ℝ (EigenpairHermitianBlockCoordinates n) :=
  LinearEquiv.finrank_eq (eigenpairHermitianBlockLinearEquiv n)

/-- The canonical reconstruction has the paper's block matrix formula. -/
theorem eigenpairHermitianBlockLinearEquiv_symm_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (y : EigenpairHermitianBlockCoordinates n) :
    (eigenpairHermitianBlockLinearEquiv n).symm y =
      decodeEigenpairHermitianBlocks y := rfl

/-- The canonical tangent differential's off-diagonal component is the gap
matrix action.  This is the moving-frame derivative needed after composing the
block split with a projective Householder coordinate. -/
theorem eigenpairHermitianBlock_movingFrame_offdiagDerivative
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) :
    (eigenpairCanonicalCoordinateDifferential E B (0, (0, z))).2.2 =
      eigenpairGapMatrix E B *ᵥ z := by
  rfl

/-- Consequently the off-diagonal moving-frame derivative has the exact local
real Jacobian density used by the coarea assembly. -/
theorem eigenpairHermitianBlock_offdiagDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    eigenpairLocalRealJacobianDensity E B =
      Complex.normSq (eigenpairGapMatrix E B).det :=
  eigenpairLocalRealJacobianDensity_eq_normSq_det E B

end CoareaNative.BlockBand
