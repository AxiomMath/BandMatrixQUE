module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
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

namespace ERNative.BlockBand

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

end ERNative.BlockBand
