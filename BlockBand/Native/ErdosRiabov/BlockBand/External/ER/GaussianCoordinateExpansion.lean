module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ConcreteExpansion
public import BlockBand.Native.ErdosRiabov.BlockBand.Model.GaussianRing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Basis

/-!
# Gaussian coordinate expansion for the ER resolvent equation

This module performs the coordinate algebra that precedes fluctuation averaging.
For one strictly upper-triangular entry it defines the exact Hermitian real and
imaginary basis directions, removes those coordinates from a matrix,
and reconstructs the matrix from the background and the two real coordinates.
It then records exact inverse-matrix first/second variations.

There is no centered norm, stochastic-domination hypothesis, moment hypothesis,
or local-law input in this file.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERGaussianCoordinate

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
## Hermitian coordinate directions
-/

/-- Real direction of an off-diagonal Hermitian coordinate:
`E_xy + E_yx`. -/
def realDirection {ι : Type*} [DecidableEq ι] (x y : ι) : Matrix ι ι ℂ :=
  Matrix.single x y 1 + Matrix.single y x 1

/-- Imaginary direction of an off-diagonal Hermitian coordinate:
`i E_xy - i E_yx`. -/
def imaginaryDirection {ι : Type*} [DecidableEq ι] (x y : ι) : Matrix ι ι ℂ :=
  Matrix.single x y Complex.I + Matrix.single y x (-Complex.I)

/-- The real coordinate direction is Hermitian. -/
theorem realDirection_isHermitian
    {ι : Type*} [DecidableEq ι] (x y : ι) :
    (realDirection x y).IsHermitian := by
  simp [realDirection, Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, add_comm]

/-- The imaginary coordinate direction is Hermitian. -/
theorem imaginaryDirection_isHermitian
    {ι : Type*} [DecidableEq ι] (x y : ι) :
    (imaginaryDirection x y).IsHermitian := by
  simp [imaginaryDirection, Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, add_comm]

/-- Remove the real and imaginary parts of one upper-triangular entry. -/
def offdiagBackground {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (x y : ι) : Matrix ι ι ℂ :=
  H - (H x y).re • realDirection x y -
    (H x y).im • imaginaryDirection x y

/-- Reinsert two real coordinates into their Hermitian directions. -/
def coordinateMatrix {ι : Type*} [DecidableEq ι]
    (B : Matrix ι ι ℂ) (x y : ι) (r s : ℝ) : Matrix ι ι ℂ :=
  B + r • realDirection x y + s • imaginaryDirection x y

/-- Exact pointwise decomposition of a matrix into background, real
coordinate and imaginary coordinate. -/
theorem offdiag_coordinate_decomposition
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ) (x y : ι) :
    coordinateMatrix (offdiagBackground H x y) x y (H x y).re (H x y).im = H := by
  simp [coordinateMatrix, offdiagBackground]
  abel

/-- The removed background has zero `(x,y)` entry for an off-diagonal
coordinate `x ≠ y`. -/
theorem offdiagBackground_apply
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ)
    {x y : ι} (hxy : x ≠ y) : offdiagBackground H x y x y = 0 := by
  simp [offdiagBackground, realDirection, imaginaryDirection,
    hxy, hxy.symm, Complex.ext_iff]

/-- Removing a coordinate from a Hermitian matrix leaves a Hermitian
background. -/
theorem offdiagBackground_isHermitian
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (x y : ι) : (offdiagBackground H x y).IsHermitian := by
  exact (hH.sub ((realDirection_isHermitian x y).smul
      (RCLike.conj_ofReal (H x y).re))).sub
    ((imaginaryDirection_isHermitian x y).smul
      (RCLike.conj_ofReal (H x y).im))

/-- Every coordinate reconstruction from a Hermitian background is Hermitian. -/
theorem coordinateMatrix_isHermitian
    {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (x y : ι) (r s : ℝ) : (coordinateMatrix B x y r s).IsHermitian := by
  exact (hB.add ((realDirection_isHermitian x y).smul
      (RCLike.conj_ofReal r))).add
    ((imaginaryDirection_isHermitian x y).smul (RCLike.conj_ofReal s))

/-- Applied to a Gaussian-ring sample, the coordinate reconstruction is the
random matrix itself, pointwise in the sample. -/
theorem actual_offdiag_coordinate_decomposition
    {p : Params} (M : Law p) (x y : Site p.n p.W) (ω : M.Ω) :
    coordinateMatrix (offdiagBackground (M.H ω) x y) x y
      (M.H ω x y).re (M.H ω x y).im = M.H ω :=
  offdiag_coordinate_decomposition (M.H ω) x y

/-- The random background obtained by removing one coordinate is Hermitian
pointwise. -/
theorem actual_offdiagBackground_isHermitian
    {p : Params} (M : Law p) (x y : Site p.n p.W) (ω : M.Ω) :
    (offdiagBackground (M.H ω) x y).IsHermitian :=
  offdiagBackground_isHermitian (M.H ω) (M.isHermitian ω) x y

/-- The exact Gaussian-ring law supplies the two normalized real component laws
and their independence for every strict upper coordinate. -/
theorem actual_coordinate_laws
    {p : Params} (M : Law p) (x y : Site p.n p.W)
    (hxy : siteLE p x y) (hne : x ≠ y) :
    HasLaw (fun ω => (M.H ω x y).re)
        (gaussianReal 0
          ⟨ERProfile.siteCovariance p x y / 2,
            div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩) M.P ∧
    HasLaw (fun ω => (M.H ω x y).im)
        (gaussianReal 0
          ⟨ERProfile.siteCovariance p x y / 2,
            div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩) M.P ∧
    IndepFun (fun ω => (M.H ω x y).re) (fun ω => (M.H ω x y).im) M.P := by
  exact ⟨by simpa [ERProfile.siteCovariance] using M.offdiag_re_law x y hxy hne,
    by simpa [ERProfile.siteCovariance] using M.offdiag_im_law x y hxy hne,
    M.offdiag_components_independent x y hxy hne⟩

/-!
## Exact inverse-matrix coordinate variations
-/

/-- Source-sign inverse `(A-zI)⁻¹`. -/
def sourceInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (A - z • (1 : Matrix ι ι ℂ))⁻¹

/-- Exact quadratic remainder around the inverse derivative `-G D G`. -/
theorem sourceInverse_secondOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (z t : ℂ)
    (hA : IsUnit (A - z • (1 : Matrix ι ι ℂ)))
    (hAt : IsUnit (A + t • D - z • (1 : Matrix ι ι ℂ))) :
    sourceInverse (A + t • D) z - sourceInverse A z +
        t • (sourceInverse A z * D * sourceInverse A z) =
      t ^ 2 • (sourceInverse A z * D * sourceInverse A z * D *
        sourceInverse (A + t • D) z) := by
  have h := ERLocalLaw.nonsingInv_secondOrder
    (A - z • (1 : Matrix ι ι ℂ))
    (A + t • D - z • (1 : Matrix ι ι ℂ)) hA hAt
  rw [show (A + t • D - z • (1 : Matrix ι ι ℂ)) -
      (A - z • (1 : Matrix ι ι ℂ)) = t • D by abel] at h
  simpa [sourceInverse, mul_assoc, pow_two, smul_smul] using h

/-- Multiplication by the real Hermitian direction produces the two expected
resolvent contractions. -/
theorem mul_realDirection_mul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (u v x y : ι) :
    (G * realDirection x y * G) u v =
      G u x * G y v + G u y * G x v := by
  have single_contraction (a b : ι) (c : ℂ) :
      (G * Matrix.single a b c * G) u v = G u a * c * G b v := by
    classical
    rw [mul_assoc]
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [Matrix.single_mul_apply_same]
      ring
    · intro j _ hja
      rw [Matrix.single_mul_apply_of_ne c a b j v hja G]
      simp
    · simp
  rw [realDirection, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.add_apply]
  rw [single_contraction, single_contraction]
  ring

/-- Multiplication by the imaginary Hermitian direction gives the signed pair
of contractions. -/
theorem mul_imaginaryDirection_mul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (u v x y : ι) :
    (G * imaginaryDirection x y * G) u v =
      Complex.I * G u x * G y v - Complex.I * G u y * G x v := by
  have single_contraction (a b : ι) (c : ℂ) :
      (G * Matrix.single a b c * G) u v = G u a * c * G b v := by
    classical
    rw [mul_assoc]
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [Matrix.single_mul_apply_same]
      ring
    · intro j _ hja
      rw [Matrix.single_mul_apply_of_ne c a b j v hja G]
      simp
    · simp
  rw [imaginaryDirection, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.add_apply]
  rw [single_contraction, single_contraction]
  ring

/-!
## Coordinatewise IBP and circular recombination
-/

end ERGaussianCoordinate
end GaussianRing
end ERNative.BlockBand
