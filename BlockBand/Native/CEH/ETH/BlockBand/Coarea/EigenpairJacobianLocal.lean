module

public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.EigenpairCoordinates
public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.ProjectiveChartIntegral

/-!
# Local eigenpair-coordinate Jacobian

This module packages the local content of the eigenpair Jacobian lemma.  At the canonical selected direction, the differential is
block triangular: the energy and complementary-matrix coordinates are unchanged,
while the complex projective tangent coordinate is multiplied by `E I - B`.  Its
real density is the square of the complex norm determinant, hence the squared gap
determinant.  The independently proved projective-chart integral supplies the
factor `π^(d-1)/(d-1)!`.

No global manifold chart, multiplicity count, or coarea/change-of-variables theorem
is asserted here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix MeasureTheory

/-- The canonical local coordinate differential.

The source and target coordinates are `(δE, δB, δz)`: a real eigenvalue direction,
a complex complementary-matrix direction, and a complex projective tangent direction.
The first two diagonal blocks are identities and the third is multiplication by the
gap matrix `E I - B`.  All complex spaces are regarded as real spaces in this map. -/
def eigenpairCanonicalCoordinateDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    (ℝ × (Matrix n n ℂ × (n → ℂ))) →ₗ[ℝ]
      (ℝ × (Matrix n n ℂ × (n → ℂ))) where
  toFun ξ :=
    (ξ.1, (ξ.2.1,
      (eigenpairOffdiagLinearMap E B).restrictScalars ℝ ξ.2.2))
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- The canonical differential is block diagonal, hence block triangular, in
`(δE, δB, δz)` coordinates.  The only nonidentity diagonal block is `E I - B` on
the projective tangent coordinate. -/
theorem eigenpairCanonicalCoordinateDifferential_triangular
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ)
    (ξ : ℝ × (Matrix n n ℂ × (n → ℂ))) :
    eigenpairCanonicalCoordinateDifferential E B ξ =
      (ξ.1, (ξ.2.1, eigenpairGapMatrix E B *ᵥ ξ.2.2)) := by
  rfl

/-- Real Jacobian density of the projective tangent block, expressed as the squared
modulus of its complex determinant.

For a complex-linear endomorphism this squared determinant modulus is its
real `2n`-dimensional volume density.  Defining the local density this way avoids
asserting a global chart change-of-variables theorem. -/
def eigenpairLocalRealJacobianDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) : ℝ :=
  eigenpairOffdiagJacobian E B

/-- The local real density is the squared modulus of the determinant of the
complex-linear tangent block in the canonical differential. -/
theorem eigenpairLocalRealJacobianDensity_eq_det_differential
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    eigenpairLocalRealJacobianDensity E B =
      Complex.normSq (LinearMap.det (eigenpairOffdiagLinearMap E B)) := by
  rw [eigenpairLocalRealJacobianDensity, eigenpairOffdiagJacobian,
    det_eigenpairOffdiagLinearMap]

/-- The real tangent density equals the squared modulus of the complex gap
determinant. -/
theorem eigenpairLocalRealJacobianDensity_eq_normSq_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) :
    eigenpairLocalRealJacobianDensity E B =
      Complex.normSq (eigenpairGapMatrix E B).det := by
  rw [eigenpairLocalRealJacobianDensity_eq_det_differential,
    det_eigenpairOffdiagLinearMap]

/-- For a Hermitian complementary block the local real Jacobian is exactly the
square of the real gap determinant, `det(B-E)^2`.  The opposite
sign convention `E-B` is immaterial after squaring. -/
theorem eigenpairLocalRealJacobianDensity_eq_detGap_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    eigenpairLocalRealJacobianDensity E B =
      (eigenpairGapMatrix E B).det.re ^ 2 := by
  rw [eigenpairLocalRealJacobianDensity_eq_normSq_det]
  exact eigenpairOffdiagJacobian_eq_det_re_sq E hB

/-- The normalized projective affine chart has total density
`π^(d-1)/(d-1)!` in positive chart dimension. -/
theorem eigenpairLocalProjectiveChartMass
    (d : ℕ) (hd : 1 < d) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ d) =
      Real.pi ^ (d - 1) / (d - 1).factorial := by
  exact eigenpairProjectiveChartNormalization d hd

/-- Paper-facing local eigenpair-Jacobian formula.

For a Hermitian `(d-1) × (d-1)` complementary block, integrating the canonical
local tangent density over the normalized projective affine chart gives
`π^(d-1)/(d-1)!` times the squared spectral-gap determinant.  This is only the
local density-and-normalization statement; it does not claim the global
sum over eigenpairs or a manifold coarea formula. -/
theorem eigenpairJacobianLocalFormula
    {d : ℕ} (hd : 1 < d) (E : ℝ)
    {B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ} (hB : B.IsHermitian) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ d) *
        eigenpairLocalRealJacobianDensity E B =
      (Real.pi ^ (d - 1) / (d - 1).factorial) *
        (eigenpairGapMatrix E B).det.re ^ 2 := by
  rw [eigenpairLocalProjectiveChartMass d hd,
    eigenpairLocalRealJacobianDensity_eq_detGap_sq E hB]

end CEHNative.BlockBand
