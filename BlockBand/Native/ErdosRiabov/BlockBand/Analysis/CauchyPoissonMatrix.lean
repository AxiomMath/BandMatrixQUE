module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.PositiveResolvent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Noncommuting matrix Cauchy–Poisson precursor

This module develops the noncommuting analytic matrix pencil behind the projected
Wegner estimate.  For Hermitian `A`, a positive-semidefinite
absorber `Q`, and `η > 0`, the pencil

`A + z Q + i η I`

has strictly positive matrix imaginary part throughout the closed upper half
plane.  We prove its invertibility there, the exact derivative of its inverse
and trace, and the nonnegativity and harmonicity of its negative-imaginary
trace in the open upper half plane.  These statements do not assume that `A`
and `Q` commute.

The remaining steps to the Cauchy-average identity are the
explicit bound `-Im Tr R(z) ≤ card ι / η` and a bounded upper-half-plane
Poisson representation theorem.  Mathlib currently supplies the local
harmonicity constructions but no such global boundary representation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

namespace ERNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The noncommuting matrix pencil used in the PSSS Poisson argument. -/
def cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (η : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  A + z • Q + Complex.I • (η • (1 : Matrix ι ι ℂ))

omit [Fintype ι] in
/-- The pencil's matrix imaginary part is `Im(z) Q + η I`, without any
commutativity assumption. -/
theorem matrixImaginaryPart_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (η : ℝ) (z : ℂ) :
    matrixImaginaryPart (cauchyResolventPencil A Q η z) =
      z.im • Q + η • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp [cauchyResolventPencil, matrixImaginaryPart, hA.eq, hQ.eq]
  ring_nf
  rw [Complex.I_sq]
  simp
  apply Complex.ext <;> simp <;> ring

omit [Fintype ι] in
/-- Strict positive definiteness supplied by the regulator. -/
theorem matrixImaginaryPart_cauchyResolventPencil_posDef
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    (matrixImaginaryPart (cauchyResolventPencil A Q η z)).PosDef := by
  rw [matrixImaginaryPart_cauchyResolventPencil A Q hA hQ.isHermitian]
  exact Matrix.PosDef.posSemidef_add (hQ.smul hz)
    (Matrix.PosDef.one.smul hη)

/-- There are no poles of the regulated pencil on the closed upper half
plane. -/
theorem isUnit_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    IsUnit (cauchyResolventPencil A Q η z) :=
  isUnit_of_matrixImaginaryPart_posDef
    (matrixImaginaryPart_cauchyResolventPencil_posDef A Q hA hQ hη hz)

/-- Determinant version of pole exclusion. -/
theorem isUnit_det_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    IsUnit (cauchyResolventPencil A Q η z).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_cauchyResolventPencil A Q hA hQ hη hz)

/-- The analytic-ring inverse agrees with the matrix nonsingular inverse at
an invertible matrix.  This bridges Mathlib's Banach-algebra calculus API to
the matrix resolvent notation used elsewhere in the project. -/
theorem ringInverse_eq_nonsing_inv_of_isUnit
    (M : Matrix ι ι ℂ) (hM : IsUnit M) :
    Ring.inverse M = M⁻¹ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  rw [Ring.inverse_of_isUnit hM]
  apply hM.mul_left_cancel
  calc
    M * (↑(hM.unit⁻¹) : Matrix ι ι ℂ) =
        (↑hM.unit : Matrix ι ι ℂ) * (↑(hM.unit⁻¹) : Matrix ι ι ℂ) :=
      congrArg (fun X : Matrix ι ι ℂ =>
        X * (↑(hM.unit⁻¹) : Matrix ι ι ℂ)) hM.unit_spec.symm
    _ = 1 := Units.mul_inv hM.unit
    _ = M * M⁻¹ := (M.mul_nonsing_inv hdet).symm

end ERNative.BlockBand
