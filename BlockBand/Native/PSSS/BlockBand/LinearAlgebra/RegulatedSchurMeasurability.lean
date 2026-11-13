module

public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.MeasurableMatrixInverse
public import BlockBand.Native.PSSS.BlockBand.Analysis.SchurPositivity
public import BlockBand.Native.PSSS.BlockBand.Analysis.PositiveResolvent

/-!
# Measurable regulated Schur families

A block-matrix family whose imaginary part dominates a strictly positive multiple of
the identity has invertible full and complementary blocks.  Its Schur complement is
measurable and splits canonically into a Hermitian background plus `i` times a
positive-semidefinite absorber and the original regulator.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory
open scoped ComplexOrder

/-- Hermitian part of a finite complex matrix. -/
def matrixHermitianPart {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)

/-- The Hermitian part is Hermitian. -/
theorem matrixHermitianPart_isHermitian {ι : Type*} (A : Matrix ι ι ℂ) :
    (matrixHermitianPart A).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [matrixHermitianPart]
  ring

/-- A measurable matrix family has measurable conjugate transpose. -/
theorem Measurable.matrixConjTranspose
    {Ω m n : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix m n ℂ} (hA : Measurable A) :
    Measurable (fun ω => (A ω)ᴴ) := by
  rw [Matrix.measurable_iff]
  intro i j
  exact Complex.continuous_conj.measurable.comp
    ((Matrix.measurable_iff.mp hA) j i)

/-- Hermitian parts of measurable families are measurable. -/
theorem Measurable.matrixHermitianPart
    {Ω ι : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun ω => matrixHermitianPart (A ω)) := by
  rw [Matrix.measurable_iff]
  intro i j
  exact measurable_const.mul
    ((Matrix.measurable_iff.mp hA i j).add
      (Matrix.measurable_iff.mp (Measurable.matrixConjTranspose hA) i j))

/-- Matrix imaginary parts of measurable families are measurable. -/
theorem Measurable.matrixImaginaryPart
    {Ω ι : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun ω => matrixImaginaryPart (A ω)) := by
  rw [Matrix.measurable_iff]
  intro i j
  exact measurable_const.mul
    ((Matrix.measurable_iff.mp hA i j).sub
      (Matrix.measurable_iff.mp (Measurable.matrixConjTranspose hA) i j))

end PSSSNative.BlockBand
