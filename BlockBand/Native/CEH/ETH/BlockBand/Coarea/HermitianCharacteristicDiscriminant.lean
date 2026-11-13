module

public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.HermitianCoordinates
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.FieldTheory.Separable

/-!
# The characteristic discriminant in Hermitian coordinates

This module constructs the characteristic discriminant polynomial of the explicit
real coordinate model for complex Hermitian matrices.  Its evaluation is identified
with the matrix discriminant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix Polynomial

/-- The universal complex Hermitian matrix whose indeterminates are the explicit
real-coordinate labels.  The variables are formally complex here, while evaluation
on real values recovers `hermitianMatrixOfCoordinates`. -/
def universalHermitianMatrix (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial (HermitianCoordinate d) ℂ) :=
  fun i j =>
    if hEq : i = j then MvPolynomial.X (.inl i)
    else if hLt : i < j then
      MvPolynomial.X (.inr (.inl ⟨(i, j), hLt⟩)) +
        MvPolynomial.C Complex.I * MvPolynomial.X (.inr (.inr ⟨(i, j), hLt⟩))
    else
      MvPolynomial.X (.inr (.inl
        ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)⟩)) -
        MvPolynomial.C Complex.I * MvPolynomial.X (.inr (.inr
          ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)⟩))

/-- The characteristic discriminant of the universal Hermitian coordinate matrix. -/
def hermitianCharacteristicDiscriminantComplex (d : ℕ) :
    MvPolynomial (HermitianCoordinate d) ℂ :=
  (universalHermitianMatrix d).discr

/-- Polynomial discriminants of monic polynomials commute with coefficient
homomorphisms into a nontrivial ring. -/
theorem Polynomial.discr_map_of_monic {R S : Type*}
    [CommRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (p : R[X]) (hp : p.Monic) :
    (p.map f).discr = f p.discr := by
  rw [Polynomial.discr, Polynomial.discr]
  have hd : (p.map f).natDegree = p.natDegree := hp.natDegree_map f
  let e : Fin ((p.map f).natDegree - 1 + (p.map f).natDegree) ≃
      Fin (p.natDegree - 1 + p.natDegree) := finCongr (by omega)
  have hm : (p.map f).sylvesterDeriv.reindex e e =
      (p.sylvesterDeriv).map f := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix, Polynomial.sylvesterDeriv,
      Polynomial.sylvester, e, hd]
    split_ifs <;> simp_all [Matrix.updateRow_apply, Fin.addCases]
    split_ifs <;> simp_all
  rw [← Matrix.det_reindex_self e, hm, map_mul, map_pow, map_neg, map_one, hd]
  change (RingHom.mapMatrix f p.sylvesterDeriv).det * _ = _
  rw [RingHom.map_det]

/-- Evaluation of the universal coordinate matrix at real coordinate values
recovers the concrete Hermitian reconstruction. -/
theorem eval_universalHermitianMatrix {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    (universalHermitianMatrix d).map
        (MvPolynomial.eval fun c => (x c : ℂ)) =
      hermitianMatrixOfCoordinates x := by
  ext i j
  by_cases hEq : i = j
  · subst j
    simp [universalHermitianMatrix, hermitianMatrixOfCoordinates]
  · by_cases hLt : i < j
    · simp [universalHermitianMatrix, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, hEq, hLt]
      ring
    · simp [universalHermitianMatrix, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, hEq, hLt]
      ring

/-- Evaluation of the coordinate discriminant is exactly the discriminant of
the reconstructed Hermitian matrix. -/
theorem eval_hermitianCharacteristicDiscriminantComplex {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    MvPolynomial.eval (fun c => (x c : ℂ))
        (hermitianCharacteristicDiscriminantComplex d) =
      (hermitianMatrixOfCoordinates x).discr := by
  let ev : MvPolynomial (HermitianCoordinate d) ℂ →+* ℂ :=
    MvPolynomial.eval fun c => (x c : ℂ)
  calc
    ev (hermitianCharacteristicDiscriminantComplex d) =
        (((universalHermitianMatrix d).charpoly).map ev).discr := by
      rw [hermitianCharacteristicDiscriminantComplex, Matrix.discr]
      exact (Polynomial.discr_map_of_monic ev _
        (Matrix.charpoly_monic (universalHermitianMatrix d))).symm
    _ = ((universalHermitianMatrix d).map ev).discr := by
      rw [Matrix.discr, Matrix.charpoly_map]
    _ = (hermitianMatrixOfCoordinates x).discr := by
      rw [eval_universalHermitianMatrix]

/-- A monic separable polynomial over a field has nonzero discriminant. -/
theorem Polynomial.discr_ne_zero_of_monic_separable
    {p : ℂ[X]} (hp : p.Monic) (hsep : p.Separable) : p.discr ≠ 0 := by
  by_cases hdeg : p.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg]
    intro h
    have hC := Polynomial.discr_C (1 : ℂ)
    rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, hC] at h
    exact one_ne_zero h
  · have hpos : 0 < p.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    have hr : IsUnit (p.resultant p.derivative) :=
      (Polynomial.isUnit_resultant_iff_isCoprime hp).2 hsep
    rw [Polynomial.natDegree_derivative] at hr
    have heq := Polynomial.resultant_deriv hpos
    rw [hp.leadingCoeff, mul_one] at heq
    intro hd
    rw [hd, mul_zero] at heq
    exact hr.ne_zero heq

/-- A canonical coordinate point whose reconstructed matrix is diagonal with
entries `0, 1, ..., d - 1`. -/
def distinctDiagonalHermitianCoordinates (d : ℕ) :
    HermitianCoordinate d → ℝ
  | .inl i => i
  | .inr _ => 0

/-- Reconstruction of the canonical witness is the diagonal matrix with
pairwise distinct natural-number entries. -/
theorem hermitianMatrixOfCoordinates_distinctDiagonal (d : ℕ) :
    hermitianMatrixOfCoordinates (distinctDiagonalHermitianCoordinates d) =
      Matrix.diagonal (fun i : Fin d => (i : ℂ)) := by
  ext i j
  by_cases hEq : i = j
  · subst j
    simp [hermitianMatrixOfCoordinates, distinctDiagonalHermitianCoordinates]
  · by_cases hLt : i < j
    · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry,
        distinctDiagonalHermitianCoordinates, hEq, hLt, Matrix.diagonal]
    · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry,
        distinctDiagonalHermitianCoordinates, hEq, hLt, Matrix.diagonal]

/-- The characteristic polynomial of the canonical diagonal witness is
separable, since its roots are the pairwise distinct natural-number entries. -/
theorem charpoly_distinctDiagonal_separable (d : ℕ) :
    (Matrix.diagonal (fun i : Fin d => (i : ℂ))).charpoly.Separable := by
  rw [Matrix.charpoly_diagonal]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  intro i j hij
  exact Fin.ext (Nat.cast_injective (R := ℂ) hij)

/-- The complex coordinate discriminant is a nonzero multivariate polynomial,
witnessed by the diagonal point `0, 1, ..., d - 1`. -/
theorem hermitianCharacteristicDiscriminantComplex_ne_zero (d : ℕ) :
    hermitianCharacteristicDiscriminantComplex d ≠ 0 := by
  intro hzero
  have heval := eval_hermitianCharacteristicDiscriminantComplex
    (distinctDiagonalHermitianCoordinates d)
  rw [hzero, map_zero, hermitianMatrixOfCoordinates_distinctDiagonal] at heval
  rw [Matrix.discr] at heval
  exact (Polynomial.discr_ne_zero_of_monic_separable
    (Matrix.charpoly_monic _) (charpoly_distinctDiagonal_separable d)) heval.symm

/-- For a monic complex polynomial, vanishing of the discriminant is exactly
failure of separability, i.e. the algebraic repeated-root condition. -/
theorem Polynomial.discr_eq_zero_iff_not_separable
    {p : ℂ[X]} (hp : p.Monic) :
    p.discr = 0 ↔ ¬p.Separable := by
  constructor
  · intro hd hsep
    exact (Polynomial.discr_ne_zero_of_monic_separable hp hsep) hd
  · intro hnsep
    by_contra hd
    by_cases hdeg : p.natDegree = 0
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg] at hnsep
      exact hnsep Polynomial.separable_one
    · have hpos : 0 < p.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
      have heq := Polynomial.resultant_deriv hpos
      rw [hp.leadingCoeff, mul_one] at heq
      have hrneFixed :
          p.resultant p.derivative p.natDegree (p.natDegree - 1) ≠ 0 := by
        rw [heq]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hd
      have hrne : p.resultant p.derivative ≠ 0 := by
        rw [Polynomial.natDegree_derivative]
        exact hrneFixed
      have hrunit : IsUnit (p.resultant p.derivative) :=
        (isUnit_iff_ne_zero.mpr hrne)
      exact hnsep ((Polynomial.isUnit_resultant_iff_isCoprime hp).mp hrunit)

/-- The matrix discriminant detects precisely failure of separability of the
characteristic polynomial.  For Hermitian matrices, this is the algebraic
repeated-spectrum condition. -/
theorem hermitian_discr_eq_zero_iff_not_charpoly_separable {d : ℕ}
    (A : HermitianMatrix (Fin d)) :
    A.1.discr = 0 ↔ ¬A.1.charpoly.Separable := by
  rw [Matrix.discr]
  exact Polynomial.discr_eq_zero_iff_not_separable (Matrix.charpoly_monic A.1)

end CEHNative.BlockBand
