module

public import BlockBand.Native.PSSS.BlockBand.Coarea.HouseholderEigenpairCoordinates
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Selected-coordinate Hermitian eigenpair charts

This module transports the canonical `Unit ⊕ Fin (d-1)` eigenpair block split
to an arbitrary distinguished coordinate of `Fin d`.  The distinguished index
is sent to the `Unit` summand and `Fin.succAbove` supplies the complementary
indices.  Reindexing preserves Hermitian matrices and gives a real-linear
equivalence with the energy/tangent/complement coordinate space.

This is the discrete reindexing and dimension bookkeeping needed by the
phase-fixed Householder construction.  A smooth chart additionally needs the
full real derivative of the coordinate-dependent Householder conjugation in
affine projective coordinates, which is not part of this module.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix

/-- Unitary conjugation restricted to the real vector space of Hermitian
matrices. -/
def realHermitianUnitaryConjugationLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) :
    RealHermitianMatrix ι ≃ₗ[ℝ] RealHermitianMatrix ι where
  toFun A := ⟨Hᴴ * A.1 * H, isHermitian_unitaryConjugation H A.1 A.2⟩
  invFun A :=
    ⟨H * A.1 * Hᴴ, by
      change (H * A.1 * Hᴴ).IsHermitian
      simpa using isHermitian_unitaryConjugation Hᴴ A.1 A.2⟩
  left_inv A := by
    apply Subtype.ext
    change H * (Hᴴ * A.1 * H) * Hᴴ = A.1
    exact (unitaryConjugationLinearEquiv H hH).left_inv A.1
  right_inv A := by
    apply Subtype.ext
    change Hᴴ * (H * A.1 * Hᴴ) * H = A.1
    exact (unitaryConjugationLinearEquiv H hH).right_inv A.1
  map_add' A B := by
    apply Subtype.ext
    exact (unitaryConjugationLinearEquiv H hH).map_add A.1 B.1
  map_smul' c A := by
    apply Subtype.ext
    change Hᴴ * ((c : ℂ) • A.1) * H =
      (c : ℂ) • (Hᴴ * A.1 * H)
    exact (unitaryConjugationLinearEquiv H hH).map_smul (c : ℂ) A.1

end PSSSNative.BlockBand
