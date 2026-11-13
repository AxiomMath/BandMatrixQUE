module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairSmoothDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Euclidean transport of nonlinear eigenpair coordinates

This module transports the nonlinear selected-eigenpair decoder from the
paper's finite real Hermitian coordinates to `EuclideanSpace`.  The transport
is exact on zero-projective slices; its algebraic differential has the exact
squared-gap Jacobian, and every nonzero-gap differential is promoted to a
continuous linear automorphism, the input expected by an inverse-function
theorem.

There is a subtlety in Mathlib.  `EuclideanSpace` itself is a
`WithLp` finite function type and exposes two non-definitionally-equal paths to
its additive/module structures (`WithLp.instModule` and the module field of
`PiLp.normedSpace`).  Thus replacing the `Pi` carrier does **not**
allow the projective-unit Fréchet derivative to compose with
this transport: the source mismatch has moved to the intermediate complex
Euclidean/projective `Pi` spaces.  An analytic atlas must therefore use a newtype
for all three carriers (real Hermitian coordinates, complex projective
coordinates, and complex unit vectors) with single coherent structures, and
transport the projective derivative chain to it.  No global instance and no local
diffeomorphism are introduced here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- Euclidean analytic coordinates with the same finite index as the paper's
Hermitian coordinate function space. -/
abbrev HermitianEuclideanCoordinateSpace (d : ℕ) :=
  EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate d)))

/-- Canonical continuous coordinate identification. -/
def hermitianEuclideanCoordinateEquiv (d : ℕ) :
    HermitianEuclideanCoordinateSpace d ≃L[ℝ] HermitianCoordinateSpace d :=
  EuclideanSpace.equiv _ ℝ

/-- The selected block decomposition as a linear equivalence from Euclidean
coordinates. -/
def selectedEigenpairEuclideanBlockLinearEquiv {d : ℕ} (i : Fin d) :
    HermitianEuclideanCoordinateSpace d ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) where
  toFun x := selectedEigenpairFinCoordinateLinearEquiv i
    (hermitianEuclideanCoordinateEquiv d x)
  invFun y := (hermitianEuclideanCoordinateEquiv d).symm
    ((selectedEigenpairFinCoordinateLinearEquiv i).symm y)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The nonlinear selected-eigenpair decoder transported to Euclidean
coordinates on source and target. -/
def selectedEigenpairEuclideanChartDecode {d : ℕ} (i : Fin d) :
    HermitianEuclideanCoordinateSpace d →
      HermitianEuclideanCoordinateSpace d :=
  fun x => (hermitianEuclideanCoordinateEquiv d).symm
    (selectedEigenpairFinCoordinateChartDecode i
      (hermitianEuclideanCoordinateEquiv d x))

/-- A zero-projective slice in Euclidean coordinates. -/
def selectedEigenpairEuclideanZeroSlice {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    HermitianEuclideanCoordinateSpace d :=
  (hermitianEuclideanCoordinateEquiv d).symm
    (selectedEigenpairZeroSliceCoordinates i E B)

/-- Coordinate conjugation of the canonical block differential, natively on
the Euclidean carrier. -/
def selectedEigenpairEuclideanDifferential {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    HermitianEuclideanCoordinateSpace d →L[ℝ]
      HermitianEuclideanCoordinateSpace d :=
  let L : HermitianEuclideanCoordinateSpace d →ₗ[ℝ]
      HermitianEuclideanCoordinateSpace d :=
    { toFun := fun u => (hermitianEuclideanCoordinateEquiv d).symm
        (selectedEigenpairFinCoordinateDifferential i E B
          (hermitianEuclideanCoordinateEquiv d u))
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  L.toContinuousLinearMap

@[simp] theorem selectedEigenpairEuclideanChartDecode_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    selectedEigenpairEuclideanChartDecode i
        (selectedEigenpairEuclideanZeroSlice i E B) =
      selectedEigenpairEuclideanZeroSlice i E B := by
  simp [selectedEigenpairEuclideanChartDecode,
    selectedEigenpairEuclideanZeroSlice]

/-- The Euclidean differential is conjugation of the canonical block
coordinate differential by the selected-block equivalence. -/
theorem selectedEigenpairEuclideanDifferential_toLinearMap
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    (selectedEigenpairEuclideanDifferential i E B).toLinearMap =
      (selectedEigenpairEuclideanBlockLinearEquiv i).symm.toLinearMap.comp
        ((eigenpairHermitianBlockCoordinateDifferential E B.1).comp
          (selectedEigenpairEuclideanBlockLinearEquiv i).toLinearMap) := by
  ext u
  rfl

/-- Euclidean transport preserves the exact paper Jacobian. -/
theorem abs_det_selectedEigenpairEuclideanDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det
        (selectedEigenpairEuclideanDifferential i E B).toLinearMap| =
      eigenpairLocalRealJacobianDensity E B.1 := by
  rw [selectedEigenpairEuclideanDifferential_toLinearMap]
  rw [show LinearMap.det
      ((selectedEigenpairEuclideanBlockLinearEquiv i).symm.toLinearMap.comp
        ((eigenpairHermitianBlockCoordinateDifferential E B.1).comp
          (selectedEigenpairEuclideanBlockLinearEquiv i).toLinearMap)) =
      LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B.1) by
    simpa using LinearMap.det_conj
      (eigenpairHermitianBlockCoordinateDifferential E B.1)
      (selectedEigenpairEuclideanBlockLinearEquiv i).symm]
  exact abs_det_eigenpairHermitianBlockCoordinateDifferential E B.1

/-- Nonzero local gap density makes the Euclidean transported differential
invertible. -/
theorem det_selectedEigenpairEuclideanDifferential_ne_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : eigenpairLocalRealJacobianDensity E B.1 ≠ 0) :
    LinearMap.det
      (selectedEigenpairEuclideanDifferential i E B).toLinearMap ≠ 0 := by
  intro hzero
  have habs : |LinearMap.det
      (selectedEigenpairEuclideanDifferential i E B).toLinearMap| = 0 := by
    rw [hzero, abs_zero]
  exact hgap ((abs_det_selectedEigenpairEuclideanDifferential i E B).symm.trans habs)

/-- The invertible derivative datum required by the inverse function theorem
at every nonzero-gap slice. -/
def selectedEigenpairEuclideanDifferentialEquiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : eigenpairLocalRealJacobianDensity E B.1 ≠ 0) :
    HermitianEuclideanCoordinateSpace d ≃L[ℝ]
      HermitianEuclideanCoordinateSpace d :=
  (selectedEigenpairEuclideanDifferential i E B).toContinuousLinearEquivOfDetNeZero
    (det_selectedEigenpairEuclideanDifferential_ne_zero i E B hgap)

@[simp] theorem selectedEigenpairEuclideanDifferentialEquiv_apply
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : eigenpairLocalRealJacobianDensity E B.1 ≠ 0)
    (u : HermitianEuclideanCoordinateSpace d) :
    selectedEigenpairEuclideanDifferentialEquiv i E B hgap u =
      selectedEigenpairEuclideanDifferential i E B u := by
  exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply _ _ _

end CoareaNative.BlockBand
