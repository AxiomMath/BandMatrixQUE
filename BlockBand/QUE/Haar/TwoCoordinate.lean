module

public import BlockBand.QUE.Haar.FirstMoment
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Two-coordinate unitary rotations for the complex Haar second moment

Unitaries mixing two coordinates by a normalized Hadamard block and a phase, and the four-phase
polarization identity eliminating the nonradial fourth-degree terms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Finite two-coordinate sum with distinct indices. -/
theorem sum_two_ite {T : Type*} [AddCommMonoid T]
    (c d : A) (hcd : c ≠ d) (f g : A → T) :
    (∑ k : A, if k = c then f k else if k = d then g k else 0) = f c + g d := by
  calc
    _ = ∑ k : A, ((if k = c then f k else 0) + (if k = d then g k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkc : k = c <;> by_cases hkd : k = d <;> simp_all
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Real normalized Hadamard block embedded in two coordinates. -/
def twoCoordinateMatrix (c d : A) (r : ℝ) : Matrix A A ℂ :=
  fun i j => if i = c then
    (if j = c then (r : ℂ) else if j = d then (r : ℂ) else 0)
    else if i = d then
      (if j = c then (r : ℂ) else if j = d then -(r : ℂ) else 0)
    else if i = j then 1 else 0

/-- The embedded normalized Hadamard matrix is unitary. -/
theorem twoCoordinateMatrix_mem (c d : A) (hcd : c ≠ d) (r : ℝ)
    (hr : r ^ 2 = 1 / 2) :
    twoCoordinateMatrix c d r ∈ Matrix.unitaryGroup A ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hic : i = c <;> by_cases hid : i = d <;>
    by_cases hjc : j = c <;> by_cases hjd : j = d
  all_goals simp_all [twoCoordinateMatrix, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, ite_mul, sum_two_ite]
  all_goals simp_all only [eq_comm]
  all_goals norm_cast
  all_goals norm_num at hr ⊢
  all_goals nlinarith

/-- The Haar rotation mixing a pair of coordinates by `1/sqrt 2`. -/
def twoCoordinateUnitary (c d : A) (hcd : c ≠ d) : Matrix.unitaryGroup A ℂ :=
  ⟨twoCoordinateMatrix c d (Real.sqrt (1 / 2)),
    twoCoordinateMatrix_mem c d hcd _ (Real.sq_sqrt (by norm_num))⟩

/-- The first mixed coordinate is the normalized sum of the two old ones. -/
theorem twoCoordinateUnitary_mulVec (c d : A) (hcd : c ≠ d) (v : A → ℂ) :
    ((twoCoordinateUnitary c d hcd : Matrix A A ℂ) *ᵥ v) c =
      (Real.sqrt (1 / 2) : ℂ) * (v c + v d) := by
  simp [twoCoordinateUnitary, twoCoordinateMatrix, Matrix.mulVec, dotProduct,
    ite_mul, sum_two_ite, hcd]
  ring

/-- A single-coordinate phase matrix is unitary. -/
def phaseUnitary (d : A) (q : ℂ) (hq : q * star q = 1) :
    Matrix.unitaryGroup A ℂ :=
  ⟨Matrix.diagonal (fun i => if i = d then q else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hid : i = d
    · simpa only [hid, ite_true, starRingEnd_apply, Pi.star_apply] using hq
    · simp [hid]⟩

/-- Embedded phases change exactly the selected complex coordinate. -/
theorem phaseUnitary_mulVec (d : A) (q : ℂ) (hq : q * star q = 1)
    (v : A → ℂ) (i : A) :
    ((phaseUnitary d q hq : Matrix A A ℂ) *ᵥ v) i =
      (if i = d then q else 1) * v i := by
  exact Matrix.mulVec_diagonal _ _ _

/-- Combining a phase and a normalized Hadamard rotation gives a unitary whose first mixed
coordinate is `r(x + q y)`. -/
theorem twoCoordinate_phase_mulVec (c d : A) (hcd : c ≠ d)
    (q : ℂ) (hq : q * star q = 1) (v : A → ℂ) :
    (((twoCoordinateUnitary c d hcd * phaseUnitary d q hq :
      Matrix.unitaryGroup A ℂ) : Matrix A A ℂ) *ᵥ v) c =
      (Real.sqrt (1 / 2) : ℂ) * (v c + q * v d) := by
  rw [Matrix.UnitaryGroup.mul_val, ← Matrix.mulVec_mulVec,
    twoCoordinateUnitary_mulVec]
  simp [phaseUnitary_mulVec, hcd]

/-- Four complex phases eliminate all nonradial fourth-degree terms (for absolute-value fourth
powers). -/
theorem complex_fourth_polarization (x y : ℂ) :
    ‖x + y‖ ^ 4 + ‖x - y‖ ^ 4 +
      ‖x + Complex.I * y‖ ^ 4 + ‖x - Complex.I * y‖ ^ 4 =
      4 * (‖x‖ ^ 4 + ‖y‖ ^ 4 + 4 * (‖x‖ ^ 2 * ‖y‖ ^ 2)) := by
  simp only [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

end BlockBand.QUE.Haar
