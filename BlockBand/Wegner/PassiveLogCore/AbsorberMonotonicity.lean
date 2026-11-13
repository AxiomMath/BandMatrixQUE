module

public import BlockBand.Wegner.PassiveLogCore.PositiveResolvent
public import BlockBand.Wegner.PassiveLogCore.PassiveLogRepair
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Infinitesimal monotonicity for passive logarithmic determinants

This module proves the deterministic sign calculation underlying the passive
log bound.  If `A` is Hermitian, a positive scalar regulator is
present, and `H` is a positive-semidefinite absorber direction, then the real
part of the logarithmic Jacobi score in direction `iH` is nonnegative.

The result is infinitesimal: it supplies the exact derivative/sign input for a
subsequent integration along an ordered absorber segment.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder Matrix
open Polynomial

namespace BlockBand.Wegner.PassiveLogCore

variable {ι : Type*} [Fintype ι]

/-- The real trace pairing of two positive-semidefinite complex matrices is
nonnegative.  No commutativity of the two matrices is required. -/
theorem re_trace_mul_nonneg_of_posSemidef
    {P H : Matrix ι ι ℂ} (hP : P.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (P * H).trace.re := by
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hH
  obtain ⟨m, v, rfl⟩ := hH
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _hj
  rw [dotProduct_comm]
  exact hP.re_dotProduct_nonneg (v j)

/-- Pairing a Hermitian direction with the negative matrix imaginary part
extracts the negative imaginary part of the corresponding trace pairing. -/
theorem re_trace_neg_matrixImaginaryPart_mul
    (M H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    ((-matrixImaginaryPart M) * H).trace.re = -(M * H).trace.im := by
  rw [neg_mul, Matrix.trace_neg, Complex.neg_re, matrixImaginaryPart,
    Matrix.smul_mul, Matrix.trace_smul]
  have hstar : (Mᴴ * H).trace = star ((M * H).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq,
      Matrix.trace_mul_comm]
  rw [Matrix.sub_mul, Matrix.trace_sub, hstar]
  simp
  ring

variable [DecidableEq ι]

/-- The Jacobi score for adding `iH` to a matrix is the trace pairing of `H`
with the negative imaginary part of its inverse. -/
theorem jacobiScore_I_smul_eq
    (M H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (M⁻¹ * (Complex.I • H)).trace.re =
      ((-matrixImaginaryPart M⁻¹) * H).trace.re := by
  rw [Matrix.mul_smul, Matrix.trace_smul,
    re_trace_neg_matrixImaginaryPart_mul M⁻¹ H hH]
  simp

/-- Regulated passive-log derivative sign (local form). For a Hermitian base matrix, a
positive-semidefinite absorber, a strict regulator `η > 0`, and a positive-semidefinite direction
`H`, the real Jacobi score along the line `M + t(iH)` is nonnegative.

Here `M = A + i(Γ + ηI)`.  The regulator makes `M` invertible; the conclusion
is exactly the sign of `Re tr(M⁻¹ iH)`, i.e. the logarithmic determinant
derivative before integration in `t`. -/
theorem regulated_jacobiScore_nonneg
    (A Γ H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef) (hH : H.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    0 ≤ ((A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ)))⁻¹ *
      (Complex.I • H)).trace.re := by
  let M := A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))
  have hM : IsUnit M.det :=
    isUnit_det_add_I_smul_add_pos_regulator hA hΓ hη
  have him : (matrixImaginaryPart M).PosSemidef := by
    rw [matrixImaginaryPart_add_I_smul A
      (Γ + η • (1 : Matrix ι ι ℂ)) hA]
    · exact hΓ.add (Matrix.PosSemidef.one.smul hη.le)
    · exact (hΓ.add (Matrix.PosSemidef.one.smul hη.le)).isHermitian
  have hinvIm : (-matrixImaginaryPart M⁻¹).PosSemidef :=
    neg_matrixImaginaryPart_nonsing_inv_posSemidef M hM him
  rw [jacobiScore_I_smul_eq M H hH.isHermitian]
  exact re_trace_mul_nonneg_of_posSemidef hinvIm hH

/-- Infinitesimal `0 ≤ Q ≤ I` specialization.  The Loewner interval is
encoded without ambiguity by the two explicit hypotheses `Q.PosSemidef` and
`(I - Q).PosSemidef`.  Hence both the `Q` segment and its complementary
segment toward the full absorber have nonnegative regulated Jacobi score. -/
theorem regulated_Q_and_complement_jacobiScores_nonneg
    (A Γ Q : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef)
    (hQ : Q.PosSemidef)
    (hIQ : ((1 : Matrix ι ι ℂ) - Q).PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    0 ≤ ((A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ)))⁻¹ *
        (Complex.I • Q)).trace.re ∧
      0 ≤ ((A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ)))⁻¹ *
        (Complex.I • ((1 : Matrix ι ι ℂ) - Q))).trace.re :=
  ⟨regulated_jacobiScore_nonneg A Γ Q hA hΓ hQ hη,
    regulated_jacobiScore_nonneg A Γ ((1 : Matrix ι ι ℂ) - Q)
      hA hΓ hIQ hη⟩

/-- Formal-polynomial Jacobi numerator for the regulated absorbed line.  This
records both the exact derivative identity and its nonnegative normalized real
part, without invoking analytic differentiation of `log`. -/
theorem regulated_detLinePoly_derivative_and_sign
    (A Γ H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.PosSemidef) (hH : H.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    let M := A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))
    (derivative (detLinePoly M (Complex.I • H))).eval 0 =
        M.det * (M⁻¹ * (Complex.I • H)).trace ∧
      0 ≤ (M⁻¹ * (Complex.I • H)).trace.re := by
  dsimp
  have hM := isUnit_det_add_I_smul_add_pos_regulator hA hΓ hη
  exact ⟨eval_derivative_detLinePoly _ _ hM,
    regulated_jacobiScore_nonneg A Γ H hA hΓ hH hη⟩

end BlockBand.Wegner.PassiveLogCore
