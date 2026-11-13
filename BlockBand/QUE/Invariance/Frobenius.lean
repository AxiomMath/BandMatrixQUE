module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic

/-!
# Unitary invariance of the rectangular Frobenius norm

The squared Frobenius norm of a rectangular complex matrix is invariant under left and right
multiplication by unitaries.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Squared complex Frobenius norm, with no dimension normalization. -/
def frobeniusSq (A : Matrix ι κ ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

theorem frobeniusSq_eq_trace (A : Matrix ι κ ℂ) :
    frobeniusSq A = (Matrix.trace (Aᴴ * A)).re := by
  unfold frobeniusSq
  rw [Finset.sum_comm]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply]

/-- Left multiplication by a unitary preserves rectangular Frobenius norm. -/
theorem frobeniusSq_unitary_left [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι κ ℂ) :
    frobeniusSq ((U : Matrix ι ι ℂ) * A) = frobeniusSq A := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace, Matrix.conjTranspose_mul]
  have hm : (Aᴴ * (U : Matrix ι ι ℂ)ᴴ) * ((U : Matrix ι ι ℂ) * A) =
      Aᴴ * ((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) * A := by
    simp only [Matrix.mul_assoc]
  have hu : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  rw [hm, hu, Matrix.mul_one]

/-- Right multiplication by a unitary preserves rectangular Frobenius norm. -/
theorem frobeniusSq_unitary_right [DecidableEq κ] (V : Matrix.unitaryGroup κ ℂ) (A : Matrix ι κ ℂ) :
    frobeniusSq (A * (V : Matrix κ κ ℂ)) = frobeniusSq A := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace, Matrix.conjTranspose_mul]
  have hm : ((V : Matrix κ κ ℂ)ᴴ * Aᴴ) * (A * (V : Matrix κ κ ℂ)) =
      (V : Matrix κ κ ℂ)ᴴ * (Aᴴ * A) * (V : Matrix κ κ ℂ) := by
    simp only [Matrix.mul_assoc]
  rw [hm, Matrix.trace_mul_cycle]
  have hv : (V : Matrix κ κ ℂ) * (V : Matrix κ κ ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.prop
  rw [hv, Matrix.one_mul]

/-- Left and right unitary rotations together preserve the squared Frobenius norm. -/
theorem frobeniusSq_unitary_both [DecidableEq ι] [DecidableEq κ] (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (A : Matrix ι κ ℂ) :
    frobeniusSq ((U : Matrix ι ι ℂ) * A * (V : Matrix κ κ ℂ)) = frobeniusSq A := by
  rw [frobeniusSq_unitary_right, frobeniusSq_unitary_left]

end BlockBand.QUE.Invariance
