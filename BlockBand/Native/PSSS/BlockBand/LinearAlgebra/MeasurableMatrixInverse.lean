module

public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of finite complex matrix inversion

Determinants and adjugates are polynomial in the entries.  The nonsingular inverse is
the measurable rational expression `det⁻¹ • adjugate`, with the standard totalized
inverse at singular matrices.  The parameter-dependent forms are the API needed by
the physical Schur-complement construction.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory

/-- The determinant is measurable on finite complex matrices. -/
theorem measurable_matrixDet {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A.det) :=
  (continuous_id.matrix_det).measurable

/-- The adjugate is measurable on finite complex matrices. -/
theorem measurable_matrixAdjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A.adjugate) :=
  (continuous_id.matrix_adjugate).measurable

/-- The totalized nonsingular inverse is measurable on finite complex matrices. -/
theorem measurable_matrixNonsingInv
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  rw [show (fun A : Matrix ι ι ℂ => A⁻¹) =
      fun A => (Ring.inverse A.det) • A.adjugate by
    funext A
    rfl]
  rw [Matrix.measurable_iff]
  intro i j
  simp_rw [Ring.inverse_eq_inv]
  change Measurable (fun A : Matrix ι ι ℂ =>
    A.det⁻¹ * A.adjugate i j)
  exact measurable_matrixDet.inv.mul
    ((Matrix.measurable_iff.mp measurable_matrixAdjugate) i j)

/-- Nonsingular inverses of measurable finite complex matrix families are measurable. -/
theorem Measurable.matrixNonsingInv
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun ω => (A ω)⁻¹) :=
  measurable_matrixNonsingInv.comp hA

/-- Products of measurable finite matrix families are measurable, including rectangular
families. -/
theorem Measurable.matrixMul
    {Ω m n p : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : Ω → Matrix m n ℂ} {B : Ω → Matrix n p ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun ω => A ω * B ω) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

/-- A Schur complement of measurable finite matrix families is measurable when the
complementary family is pointwise invertible. -/
theorem Measurable.schurComplement₂₂
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq n]
    {A : Ω → Matrix m m ℂ} {B : Ω → Matrix m n ℂ}
    {C : Ω → Matrix n m ℂ} {D : Ω → Matrix n n ℂ}
    [∀ ω, Invertible (D ω)]
    (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hD : Measurable D) :
    Measurable (fun ω => _root_.PSSSNative.BlockBand.schurComplement₂₂ (A ω) (B ω) (C ω) (D ω)) := by
  rw [show (fun ω => _root_.PSSSNative.BlockBand.schurComplement₂₂ (A ω) (B ω) (C ω) (D ω)) =
      fun ω => A ω - B ω * (D ω)⁻¹ * C ω by
    funext ω
    rw [_root_.PSSSNative.BlockBand.schurComplement₂₂, Matrix.invOf_eq_nonsing_inv]]
  have hBD : Measurable (fun ω => B ω * (D ω)⁻¹) :=
    Measurable.matrixMul hB (Measurable.matrixNonsingInv hD)
  have hBDC : Measurable (fun ω => B ω * (D ω)⁻¹ * C ω) :=
    Measurable.matrixMul hBD hC
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_iff.mp hA i j).sub
    (Matrix.measurable_iff.mp hBDC i j)

end PSSSNative.BlockBand
