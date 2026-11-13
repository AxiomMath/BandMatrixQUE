module

public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.HermitianCharacteristicDiscriminant

/-!
# Real coefficient descent for the Hermitian discriminant

The universal Hermitian discriminant has complex coefficients because the
coordinate matrix contains `Complex.I`.  This module descends its real and
imaginary coefficient parts to real multivariate polynomials and packages their
squared norm as the real polynomial used by the zero-set nullity theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory

/-- Take the real part of every coefficient of a complex multivariate
polynomial, without changing its monomials. -/
def mvPolynomialRealPart {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℝ :=
  p.coeff.sum fun m z => MvPolynomial.monomial m z.re

/-- Take the imaginary part of every coefficient of a complex multivariate
polynomial, without changing its monomials. -/
def mvPolynomialImagPart {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℝ :=
  p.coeff.sum fun m z => MvPolynomial.monomial m z.im

/-- Coefficientwise real-part extraction commutes with evaluation at real
variable values. -/
theorem eval_mvPolynomialRealPart {σ : Type*} (p : MvPolynomial σ ℂ)
    (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialRealPart p) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).re := by
  classical
  have hprod (m : σ →₀ ℕ) :
      (∏ i ∈ m.support, (x i : ℂ) ^ m i) =
        ((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ) := by
    norm_cast
  rw [mvPolynomialRealPart, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hre : (∏ i ∈ m.support, (x i : ℂ) ^ m i).re =
      ∏ i ∈ m.support, x i ^ m i := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).re :=
        congrArg Complex.re (hprod m)
      _ = _ := rfl
  have him : (∏ i ∈ m.support, (x i : ℂ) ^ m i).im = 0 := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).im :=
        congrArg Complex.im (hprod m)
      _ = _ := rfl
  by_cases hz : (p.coeff m).re = 0 <;>
    simp [MvPolynomial.eval_monomial, Finsupp.prod, hz, hre, him]

/-- Coefficientwise imaginary-part extraction commutes with evaluation at real
variable values. -/
theorem eval_mvPolynomialImagPart {σ : Type*} (p : MvPolynomial σ ℂ)
    (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialImagPart p) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).im := by
  classical
  have hprod (m : σ →₀ ℕ) :
      (∏ i ∈ m.support, (x i : ℂ) ^ m i) =
        ((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ) := by
    norm_cast
  rw [mvPolynomialImagPart, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  rw [← Complex.imCLM_apply, map_sum]
  simp only [Complex.imCLM_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hre : (∏ i ∈ m.support, (x i : ℂ) ^ m i).re =
      ∏ i ∈ m.support, x i ^ m i := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).re :=
        congrArg Complex.re (hprod m)
      _ = _ := rfl
  have him : (∏ i ∈ m.support, (x i : ℂ) ^ m i).im = 0 := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).im :=
        congrArg Complex.im (hprod m)
      _ = _ := rfl
  by_cases hz : (p.coeff m).im = 0 <;>
    simp [MvPolynomial.eval_monomial, Finsupp.prod, hz, hre, him]

/-- The real squared-norm polynomial associated to the complex Hermitian
characteristic discriminant. -/
def hermitianDiscriminantNormSq (d : ℕ) :
    MvPolynomial (HermitianCoordinate d) ℝ :=
  let p := hermitianCharacteristicDiscriminantComplex d
  mvPolynomialRealPart p ^ 2 + mvPolynomialImagPart p ^ 2

/-- Evaluation of the real squared-norm polynomial is the complex norm square
of the characteristic discriminant evaluation. -/
theorem eval_hermitianDiscriminantNormSq {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    MvPolynomial.eval x (hermitianDiscriminantNormSq d) =
      Complex.normSq (MvPolynomial.eval (fun i => (x i : ℂ))
        (hermitianCharacteristicDiscriminantComplex d)) := by
  rw [hermitianDiscriminantNormSq, map_add, map_pow, map_pow,
    eval_mvPolynomialRealPart, eval_mvPolynomialImagPart]
  simp [Complex.normSq, pow_two]

/-- The real norm-square polynomial vanishes exactly when the complex
coordinate discriminant vanishes. -/
theorem eval_hermitianDiscriminantNormSq_eq_zero_iff {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    MvPolynomial.eval x (hermitianDiscriminantNormSq d) = 0 ↔
      MvPolynomial.eval (fun i => (x i : ℂ))
        (hermitianCharacteristicDiscriminantComplex d) = 0 := by
  rw [eval_hermitianDiscriminantNormSq, Complex.normSq_eq_zero]

/-- In concrete Hermitian coordinates, the real norm-square polynomial
vanishes exactly when the reconstructed matrix discriminant vanishes. -/
theorem eval_hermitianDiscriminantNormSq_eq_zero_iff_discr {d : ℕ}
    (x : HermitianCoordinate d → ℝ) :
    MvPolynomial.eval x (hermitianDiscriminantNormSq d) = 0 ↔
      (hermitianMatrixOfCoordinates x).discr = 0 := by
  rw [eval_hermitianDiscriminantNormSq_eq_zero_iff,
    eval_hermitianCharacteristicDiscriminantComplex]

/-- The real norm-square discriminant polynomial is nonzero.  The proof uses
the canonical diagonal coordinate point `0, 1, ..., d - 1`. -/
theorem hermitianDiscriminantNormSq_ne_zero (d : ℕ) :
    hermitianDiscriminantNormSq d ≠ 0 := by
  intro hzero
  have hz : MvPolynomial.eval (distinctDiagonalHermitianCoordinates d)
      (hermitianDiscriminantNormSq d) = 0 := by rw [hzero, map_zero]
  rw [eval_hermitianDiscriminantNormSq_eq_zero_iff_discr,
    hermitianMatrixOfCoordinates_distinctDiagonal, Matrix.discr] at hz
  exact (Polynomial.discr_ne_zero_of_monic_separable
    (Matrix.charpoly_monic _) (charpoly_distinctDiagonal_separable d)) hz

/-- The real discriminant polynomial reindexed by the canonical finite ordinal,
which is the coordinate convention used by `volume_mvPolynomial_zeroSet`. -/
def hermitianDiscriminantNormSqFin (d : ℕ) :
    MvPolynomial (Fin (Fintype.card (HermitianCoordinate d))) ℝ :=
  MvPolynomial.rename (hermitianCoordinateEquivFin d)
    (hermitianDiscriminantNormSq d)

/-- Evaluation after finite-ordinal reindexing is evaluation in the original
Hermitian coordinate labels. -/
theorem eval_hermitianDiscriminantNormSqFin (d : ℕ)
    (x : Fin (Fintype.card (HermitianCoordinate d)) → ℝ) :
    MvPolynomial.eval x (hermitianDiscriminantNormSqFin d) =
      MvPolynomial.eval (x ∘ hermitianCoordinateEquivFin d)
        (hermitianDiscriminantNormSq d) := by
  exact MvPolynomial.eval_rename _ _ _

/-- Finite-ordinal reindexing preserves nonvanishing of the real discriminant
polynomial. -/
theorem hermitianDiscriminantNormSqFin_ne_zero (d : ℕ) :
    hermitianDiscriminantNormSqFin d ≠ 0 := by
  exact (MvPolynomial.rename_injective _
    (hermitianCoordinateEquivFin d).injective).ne
      (hermitianDiscriminantNormSq_ne_zero d)

/-- The discriminant-zero locus of complex Hermitian matrices has Lebesgue
measure zero in the explicit real coordinate chart. -/
theorem volume_hermitian_discriminant_zero_coordinates (d : ℕ) :
    volume {x : Fin (Fintype.card (HermitianCoordinate d)) → ℝ |
      (hermitianMatrixOfCoordinates
        (x ∘ hermitianCoordinateEquivFin d)).discr = 0} = 0 := by
  rw [show {x : Fin (Fintype.card (HermitianCoordinate d)) → ℝ |
      (hermitianMatrixOfCoordinates
        (x ∘ hermitianCoordinateEquivFin d)).discr = 0} =
      {x | MvPolynomial.eval x (hermitianDiscriminantNormSqFin d) = 0} by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      eval_hermitianDiscriminantNormSqFin,
      eval_hermitianDiscriminantNormSq_eq_zero_iff_discr]]
  exact volume_mvPolynomial_zeroSet _ _
    (hermitianDiscriminantNormSqFin_ne_zero d)

/-- Equivalently, the nonseparable-characteristic-polynomial locus—the
algebraic repeated-spectrum locus for Hermitian matrices—is null in the same
real coordinate chart. -/
theorem volume_hermitian_repeatedSpectrum_coordinates (d : ℕ) :
    volume {x : Fin (Fintype.card (HermitianCoordinate d)) → ℝ |
      ¬(hermitianMatrixOfCoordinates
        (x ∘ hermitianCoordinateEquivFin d)).charpoly.Separable} = 0 := by
  rw [show {x : Fin (Fintype.card (HermitianCoordinate d)) → ℝ |
      ¬(hermitianMatrixOfCoordinates
        (x ∘ hermitianCoordinateEquivFin d)).charpoly.Separable} =
      {x | (hermitianMatrixOfCoordinates
        (x ∘ hermitianCoordinateEquivFin d)).discr = 0} by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Matrix.discr]
    exact (Polynomial.discr_eq_zero_iff_not_separable
      (Matrix.charpoly_monic _)).symm]
  exact volume_hermitian_discriminant_zero_coordinates d

end CEHNative.BlockBand
