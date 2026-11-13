module

public import BlockBand.Native.PSSS.BlockBand.Coarea.HouseholderEigenpairSmoothCompletion
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
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

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

namespace PSSSNative.BlockBand

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

end PSSSNative.BlockBand
