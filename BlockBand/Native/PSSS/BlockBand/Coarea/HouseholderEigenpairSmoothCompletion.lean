module

public import BlockBand.Native.PSSS.BlockBand.Coarea.PhaseFixedUnitaryCompletion
public import BlockBand.Native.PSSS.BlockBand.Coarea.LagrangeProjectorCorrectness
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Finset.Max
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
public import Mathlib.MeasureTheory.Function.Jacobian
public import BlockBand.Native.PSSS.BlockBand.Probability.GaussianNormalization
public import BlockBand.Native.PSSS.BlockBand.Coarea.GaussianRegression
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Fixed-frame smooth conjugation for eigenpair charts

This module supplies the exact smooth two-sided matrix-conjugation component of
an eigenpair chart once its phase-fixed eigenline has been chosen.  Conjugation
by the explicit Householder frame is packaged as a complex continuous linear
equivalence, so its inverse identities, injectivity, and Fréchet derivative are
available without any further geometric assumption.

A full eigenpair chart further needs real coordinates that split the
conjugated Hermitian matrix into the selected energy, the `(d-1)`-dimensional
Hermitian complementary block, and the projective coordinate, together with the
derivative of the *moving* Householder frame; neither is constructed here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix

/-- Conjugation by a unitary matrix, as a complex-linear equivalence. -/
def unitaryConjugationLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ * H = 1) :
    Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ where
  toFun A := Hᴴ * A * H
  invFun A := H * A * Hᴴ
  left_inv A := by
    have hH' : H * Hᴴ = 1 := mul_eq_one_comm.mp hH
    calc
      H * (Hᴴ * A * H) * Hᴴ = (H * Hᴴ) * A * (H * Hᴴ) := by
        noncomm_ring
      _ = A := by rw [hH']; simp
  right_inv A := by
    calc
      Hᴴ * (H * A * Hᴴ) * H = (Hᴴ * H) * A * (Hᴴ * H) := by
        noncomm_ring
      _ = A := by rw [hH]; simp
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by
    ext a b
    simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    ring_nf

/-- Unitary conjugation preserves Hermitian matrices. -/
theorem isHermitian_unitaryConjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (Hᴴ * A * H).IsHermitian := by
  change (Hᴴ * A * H)ᴴ = Hᴴ * A * H
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq]
  noncomm_ring

end PSSSNative.BlockBand
