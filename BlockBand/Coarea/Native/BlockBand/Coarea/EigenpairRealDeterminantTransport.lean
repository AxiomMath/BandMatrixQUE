module

public import BlockBand.Coarea.Native.BlockBand.Coarea.MovingHouseholderConjugationDerivative
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Real determinant transport for selected eigenpair coordinates

This module closes the scalar-restriction part of the local Jacobian
calculation.  It identifies the tangent coordinate selected by an arbitrary
matrix coordinate, and proves that the determinant of the complex gap map,
when regarded as a real-linear map, is exactly its squared complex determinant
modulus.  Thus the tangent block of the real chart derivative contributes
precisely `eigenpairLocalRealJacobianDensity`, with no additional absolute-value
or orientation factor.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The tangent component of the arbitrary-selected-coordinate block split is
the lower-left column relative to the selected coordinate. -/
theorem selectedCoordinateEigenpairLinearEquiv_tangent
    {d : ℕ} (i : Fin d) (A : RealHermitianMatrix (Fin d))
    (j : Fin (d - 1)) :
    (selectedCoordinateEigenpairLinearEquiv i A).2.1 j =
      A.1 ((selectedCoordinateEquiv i).symm (Sum.inr j)) i := by
  change A.1 ((selectedCoordinateEquiv i).symm (Sum.inr j))
      ((selectedCoordinateEquiv i).symm (Sum.inl Unit.unit)) = _
  rw [show (selectedCoordinateEquiv i).symm (Sum.inl Unit.unit) = i by
    apply (selectedCoordinateEquiv i).injective
    rw [(selectedCoordinateEquiv i).apply_symm_apply,
      selectedCoordinateEquiv_apply_selected]]

/-- The complex gap action, regarded as the real tangent block appearing in
the same-dimensional Hermitian coordinate chart. -/
def eigenpairGapRealLinearMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    (n → ℂ) →ₗ[ℝ] (n → ℂ) :=
  (eigenpairOffdiagLinearMap E B).restrictScalars ℝ

/-- The transported real tangent block acts by the expected matrix-vector gap
multiplication. -/
theorem eigenpairGapRealLinearMap_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) :
    eigenpairGapRealLinearMap E B z = eigenpairGapMatrix E B *ᵥ z := by
  rfl

/-- Restriction of scalars turns the complex determinant into its algebra norm,
which for `ℂ/ℝ` is `Complex.normSq`.  Hence the real determinant of the
tangent block is exactly the local Jacobian density. -/
theorem det_eigenpairGapRealLinearMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    LinearMap.det (eigenpairGapRealLinearMap E B) =
      eigenpairLocalRealJacobianDensity E B := by
  rw [eigenpairGapRealLinearMap, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply,
    eigenpairLocalRealJacobianDensity_eq_det_differential]

/-- The complete block-coordinate differential in the ordering
`(δE, δz, δB)` used by `EigenpairHermitianBlockCoordinates`.  It is the product
of the identity energy block, the realified gap block, and the identity
complementary-Hermitian block. -/
def eigenpairHermitianBlockCoordinateDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    EigenpairHermitianBlockCoordinates n →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates n :=
  LinearMap.prodMap LinearMap.id
    (LinearMap.prodMap (eigenpairGapRealLinearMap E B) LinearMap.id)

/-- The complete differential is block diagonal: energy and complementary
matrix variations are unchanged and the tangent variation is multiplied by
`E I - B`. -/
theorem eigenpairHermitianBlockCoordinateDifferential_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ)
    (ξ : EigenpairHermitianBlockCoordinates n) :
    eigenpairHermitianBlockCoordinateDifferential E B ξ =
      (ξ.1, (eigenpairGapMatrix E B *ᵥ ξ.2.1, ξ.2.2)) := by
  rfl

/-- The two identity diagonal blocks contribute determinant one, so the full
real block-coordinate determinant is exactly the local gap density. -/
theorem det_eigenpairHermitianBlockCoordinateDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B) =
      eigenpairLocalRealJacobianDensity E B := by
  rw [eigenpairHermitianBlockCoordinateDifferential,
    LinearMap.det_prodMap, LinearMap.det_prodMap,
    LinearMap.det_id, LinearMap.det_id,
    one_mul, mul_one, det_eigenpairGapRealLinearMap]

/-- Its absolute determinant is therefore the same density, with no
orientation correction from the identity energy or complementary blocks. -/
theorem abs_det_eigenpairHermitianBlockCoordinateDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    |LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B)| =
      eigenpairLocalRealJacobianDensity E B := by
  rw [det_eigenpairHermitianBlockCoordinateDifferential]
  exact abs_of_nonneg (eigenpairOffdiagJacobian_nonneg E B)

/-- In particular the absolute real determinant contributes no sign or
orientation correction: it is already the nonnegative squared-gap density. -/
theorem abs_det_eigenpairGapRealLinearMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    |LinearMap.det (eigenpairGapRealLinearMap E B)| =
      eigenpairLocalRealJacobianDensity E B := by
  rw [det_eigenpairGapRealLinearMap]
  exact abs_of_nonneg (eigenpairOffdiagJacobian_nonneg E B)

/-- The selected-coordinate tangent block therefore has the paper's exact
squared spectral-gap determinant for a Hermitian complementary block. -/
theorem abs_det_eigenpairGapRealLinearMap_eq_detGap_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    |LinearMap.det (eigenpairGapRealLinearMap E B)| =
      (eigenpairGapMatrix E B).det.re ^ 2 := by
  rw [abs_det_eigenpairGapRealLinearMap,
    eigenpairLocalRealJacobianDensity_eq_detGap_sq E hB]

end CoareaNative.BlockBand
