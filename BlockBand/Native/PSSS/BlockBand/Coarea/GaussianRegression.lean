module

public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Complex.Basic

/-!
# Gaussian regression in canonical eigenpair coordinates

This file proves the exact Hilbert–Schmidt square separation used in the Gaussian regression
step of the eigenpair coarea theorem.  The selected eigenvector is put in
the first coordinate.  The scalar, off-diagonal, and complementary blocks are
then orthogonal for the Hilbert–Schmidt inner product, with the off-diagonal
column occurring twice in a Hermitian matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open Matrix
open scoped BigOperators

/-- Squared Hilbert–Schmidt norm, written entrywise to avoid choosing one of
the competing matrix norm instances. -/
def hilbertSchmidtNormSq
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

end PSSSNative.BlockBand
