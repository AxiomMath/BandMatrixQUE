module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Deterministic core of the passive logarithmic determinant

This module isolates two finite-dimensional identities used in the passive-log
repair.  First, it gives the exact formal-polynomial Jacobi identity for the
line `A + t Q` at an invertible matrix `A`.  Second, it reduces the full
absorber `Q = I` for a complex Hermitian matrix to its real eigenvalues.

The parameter `t` in `detLinePoly` is a formal polynomial variable.  Thus the
Jacobi identity has no analytic differentiability side conditions and can be
specialized later to real or complex curves.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped Matrix
open Polynomial

namespace BlockBand.Wegner.PassiveLogCore

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant polynomial of the affine matrix line `A + t Q`.

This is the exact algebraic precursor of the determinant derivative in the
passive-log argument. -/
noncomputable def detLinePoly [CommRing R] (A Q : Matrix ι ι R) : R[X] :=
  (A.map (C : R →+* R[X]) + (X : R[X]) • Q.map (C : R →+* R[X])).det

/-- An invertible affine matrix line factors through its base point.

This is the matrix factorization underlying Jacobi's formula. -/
theorem map_add_X_smul_eq_mul [CommRing R] (A Q : Matrix ι ι R)
    (hA : IsUnit A.det) :
    A.map (C : R →+* R[X]) + (X : R[X]) • Q.map (C : R →+* R[X]) =
      A.map (C : R →+* R[X]) * (1 + (X : R[X]) • (A⁻¹ * Q).map (C : R →+* R[X])) := by
  rw [Matrix.mul_add, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_smul]
  congr 1
  rw [← Matrix.map_mul, ← Matrix.mul_assoc, A.mul_nonsing_inv hA, Matrix.one_mul]

/-- Formal-polynomial Jacobi identity at an invertible base matrix:

`d/dt det(A + tQ)|_{t=0} = det(A) * tr(A⁻¹ Q)`.

The source is the affine line `A + tQ`; the derivative
is the formal polynomial derivative and is evaluated at zero. -/
theorem eval_derivative_detLinePoly [CommRing R] (A Q : Matrix ι ι R)
    (hA : IsUnit A.det) :
    (derivative (detLinePoly A Q)).eval 0 = A.det * (A⁻¹ * Q).trace := by
  rw [detLinePoly, map_add_X_smul_eq_mul A Q hA, Matrix.det_mul]
  have hdet : (A.map (C : R →+* R[X])).det = C A.det :=
    (RingHom.map_det (C : R →+* R[X]) A).symm
  rw [derivative_mul, eval_add, eval_mul, eval_mul, hdet]
  rw [derivative_C, eval_zero, zero_mul, zero_add, eval_C]
  rw [Matrix.derivative_det_one_add_X_smul]

section FullAbsorber

variable {A : Matrix ι ι ℂ}

/-- Full-absorber determinant reduction: shifting a Hermitian matrix by the
complex scalar `z I` shifts each (real) eigenvalue by `z`.

In the application in the paper, `z = Complex.I * s`. -/
theorem det_add_smul_one_eq_prod_eigenvalues (hA : A.IsHermitian) (z : ℂ) :
    (A + z • (1 : Matrix ι ι ℂ)).det =
      ∏ i, ((hA.eigenvalues i : ℂ) + z) := by
  apply mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
  calc
    (-1 : ℂ) ^ Fintype.card ι * (A + z • (1 : Matrix ι ι ℂ)).det =
        (-(A + z • (1 : Matrix ι ι ℂ))).det :=
      (Matrix.det_neg _).symm
    _ = (Matrix.scalar ι (-z) - A).det := by
      congr 1
      ext i j
      by_cases hij : i = j
      · simp [Matrix.scalar_apply, hij]
        ring
      · simp [Matrix.scalar_apply, hij]
    _ = A.charpoly.eval (-z) := (Matrix.eval_charpoly A (-z)).symm
    _ = (∏ i, (X - C (hA.eigenvalues i : ℂ))).eval (-z) :=
      congrArg (fun p : ℂ[X] => p.eval (-z)) hA.charpoly_eq
    _ = (-1 : ℂ) ^ Fintype.card ι *
        ∏ i, ((hA.eigenvalues i : ℂ) + z) := by
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      calc
        ∏ i, (-z - (hA.eigenvalues i : ℂ)) =
            ∏ i, ((-1 : ℂ) * ((hA.eigenvalues i : ℂ) + z)) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
        _ = (∏ _i : ι, (-1 : ℂ)) *
            ∏ i, ((hA.eigenvalues i : ℂ) + z) := Finset.prod_mul_distrib
        _ = (-1 : ℂ) ^ Fintype.card ι *
            ∏ i, ((hA.eigenvalues i : ℂ) + z) := by simp

/-- Squared-modulus form of the full-absorber reduction.  It removes
all complex arithmetic and leaves the strictly positive real factors
`λᵢ² + s²`. -/
theorem normSq_det_add_I_smul_one_eq_prod (hA : A.IsHermitian) (s : ℝ) :
    Complex.normSq ((A + (Complex.I * s) • (1 : Matrix ι ι ℂ)).det) =
      ∏ i, ((hA.eigenvalues i) ^ 2 + s ^ 2) := by
  rw [det_add_smul_one_eq_prod_eigenvalues hA]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [Complex.normSq_apply]
  ring

/-- The full absorber never creates a zero determinant away from `s = 0`.
This is the deterministic nonvanishing input needed before taking a logarithm. -/
theorem det_add_I_smul_one_ne_zero (hA : A.IsHermitian) {s : ℝ} (hs : s ≠ 0) :
    (A + (Complex.I * s) • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  rw [det_add_smul_one_eq_prod_eigenvalues hA]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi hzero
  have him := congrArg Complex.im hzero
  simp [hs] at him

end FullAbsorber

end BlockBand.Wegner.PassiveLogCore
