module

public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.MeasurableMatrixInverse
public import BlockBand.Coarea.Native.BlockBand.Analysis.SchurPositivity
public import BlockBand.Coarea.Native.BlockBand.Analysis.PositiveResolvent

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

namespace CoareaNative.BlockBand

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

/-- Every matrix is its Hermitian part plus `i` times its matrix imaginary part. -/
theorem matrix_eq_hermitianPart_add_I_smul_imaginaryPart
    {ι : Type*} (A : Matrix ι ι ℂ) :
    A = matrixHermitianPart A + Complex.I • matrixImaginaryPart A := by
  ext i j
  simp [matrixHermitianPart, matrixImaginaryPart]
  ring_nf
  rw [Complex.I_sq]
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

/-- Measurable block data with a uniform strictly positive imaginary regulator. -/
structure RegulatedBlockFamily
    (Ω m n : Type*) [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (η : ℝ) where
  A : Ω → Matrix m m ℂ
  B : Ω → Matrix m n ℂ
  C : Ω → Matrix n m ℂ
  D : Ω → Matrix n n ℂ
  measurable_A : Measurable A
  measurable_B : Measurable B
  measurable_C : Measurable C
  measurable_D : Measurable D
  eta_pos : 0 < η
  imaginary_ge : ∀ ω,
    (matrixImaginaryPart (Matrix.fromBlocks (A ω) (B ω) (C ω) (D ω)) -
      (η : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef

/-- A positive lower bound on the imaginary part makes the full matrix invertible. -/
theorem RegulatedBlockFamily.full_isUnit
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    IsUnit (Matrix.fromBlocks (h.A ω) (h.B ω) (h.C ω) (h.D ω)) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hηI : ((η : ℂ) •
      (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by simpa using h.eta_pos)
  simpa [add_comm] using hηI.add_posSemidef (h.imaginary_ge ω)

/-- The complementary diagonal block inherits the same regulator and is invertible. -/
theorem RegulatedBlockFamily.complement_imaginary_ge
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    (matrixImaginaryPart (h.D ω) -
      (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hs := (h.imaginary_ge ω).submatrix (Sum.inr : n → Sum m n)
  have heq :
      (matrixImaginaryPart (Matrix.fromBlocks (h.A ω) (h.B ω) (h.C ω) (h.D ω)) -
        (η : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).submatrix
          Sum.inr Sum.inr =
        matrixImaginaryPart (h.D ω) - (η : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matrixImaginaryPart]
    · simp [matrixImaginaryPart, hij]
  rwa [heq] at hs

/-- The regulated complementary block is invertible. -/
theorem RegulatedBlockFamily.complement_isUnit
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    IsUnit (h.D ω) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hηI : ((η : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by simpa using h.eta_pos)
  simpa [add_comm] using hηI.add_posSemidef (h.complement_imaginary_ge ω)

/-- Totalized-inverse presentation of the lower-right Schur complement. -/
def RegulatedBlockFamily.schur
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) : Matrix m m ℂ :=
  h.A ω - h.B ω * (h.D ω)⁻¹ * h.C ω

/-- The regulated Schur complement is measurable. -/
theorem RegulatedBlockFamily.measurable_schur
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) :
    Measurable h.schur := by
  have hBD : Measurable (fun ω => h.B ω * (h.D ω)⁻¹) :=
    Measurable.matrixMul h.measurable_B (Measurable.matrixNonsingInv h.measurable_D)
  have hBDC : Measurable (fun ω => h.B ω * (h.D ω)⁻¹ * h.C ω) :=
    Measurable.matrixMul hBD h.measurable_C
  rw [Matrix.measurable_iff]
  intro i j
  exact (Matrix.measurable_iff.mp h.measurable_A i j).sub
    (Matrix.measurable_iff.mp hBDC i j)

/-- The Schur absorber after removing the regulator. -/
def RegulatedBlockFamily.absorber
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) : Matrix m m ℂ :=
  matrixImaginaryPart (h.schur ω) - (η : ℂ) • (1 : Matrix m m ℂ)

/-- The Schur absorber is positive semidefinite. -/
theorem RegulatedBlockFamily.absorber_posSemidef
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    (h.absorber ω).PosSemidef := by
  let _ : Invertible (h.D ω) :=
    Classical.choice (h.complement_isUnit ω).nonempty_invertible
  have hs := schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
    (h.A ω) (h.B ω) (h.C ω) (h.D ω) h.eta_pos.le (h.imaginary_ge ω)
  simpa [RegulatedBlockFamily.absorber, RegulatedBlockFamily.schur,
    schurComplement₂₂, Matrix.invOf_eq_nonsing_inv] using hs

/-- The canonical Schur background is Hermitian. -/
def RegulatedBlockFamily.background
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) : Matrix m m ℂ :=
  matrixHermitianPart (h.schur ω)

/-- The canonical Schur background is Hermitian. -/
theorem RegulatedBlockFamily.background_isHermitian
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    (h.background ω).IsHermitian :=
  matrixHermitianPart_isHermitian _

/-- The background is measurable as a matrix-valued family. -/
theorem RegulatedBlockFamily.measurable_background
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) :
    Measurable h.background :=
  Measurable.matrixHermitianPart h.measurable_schur

/-- The Schur absorber is measurable. -/
theorem RegulatedBlockFamily.measurable_absorber
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) :
    Measurable h.absorber := by
  rw [Matrix.measurable_iff]
  intro i j
  exact (Matrix.measurable_iff.mp (Measurable.matrixImaginaryPart h.measurable_schur) i j).sub
    measurable_const

/-- Exact Hermitian-background/absorber decomposition of the Schur complement. -/
theorem RegulatedBlockFamily.schur_eq_background_add_I_smul
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {η : ℝ} (h : RegulatedBlockFamily Ω m n η) (ω : Ω) :
    h.schur ω = h.background ω +
      Complex.I • (h.absorber ω + (η : ℂ) • (1 : Matrix m m ℂ)) := by
  rw [show h.absorber ω + (η : ℂ) • (1 : Matrix m m ℂ) =
      matrixImaginaryPart (h.schur ω) by
    simp [RegulatedBlockFamily.absorber]]
  exact matrix_eq_hermitianPart_add_I_smul_imaginaryPart _

end CoareaNative.BlockBand
