module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateIndexReorganization

/-!
# Resolvent-weighted coordinate tests for the sharp Dyson expansion

This module supplies the exact derivatives needed when Gaussian integration by
parts is applied to the Hamiltonian–Green terms in the separated Dyson
identity.  Unlike the earlier coordinate test, the observable here contains a
Green entry as well as the lower even-moment factor.  Consequently its
coordinate derivative has both the inverse-matrix term and the derivative of
the lower moment.  Both circular orientations are retained explicitly.

No local-law estimate or probabilistic hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERConcrete
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The lower `2m`-moment factor left after the Dyson equation contributes one
copy of the signed fluctuation. -/
def lowerConjugateMomentTest (m : ℕ) (w : ℂ) : ℂ :=
  w ^ m * (starRingEnd ℂ w) ^ m

/-- Real derivative of the lower even-moment factor. -/
def lowerConjugateMomentDerivative (m : ℕ) (w dw : ℂ) : ℂ :=
  ((m : ℕ) : ℂ) * w ^ (m - 1) * dw * (starRingEnd ℂ w) ^ m +
    ((m : ℕ) : ℂ) * w ^ m * (starRingEnd ℂ w) ^ (m - 1) *
      starRingEnd ℂ dw

/-- The displayed lower-moment derivative is a real derivative (`HasDerivAt`). -/
theorem hasDerivAt_lowerConjugateMomentTest
    (m : ℕ) {F : ℝ → ℂ} {r : ℝ} {dF : ℂ}
    (hF : HasDerivAt F dF r) :
    HasDerivAt (fun t => lowerConjugateMomentTest m (F t))
      (lowerConjugateMomentDerivative m (F r) dF) r := by
  have h := (hF.pow m).mul (hF.star.pow m)
  convert h using 1
  · funext t
    simp [lowerConjugateMomentTest]
  · simp [lowerConjugateMomentDerivative]
    ring

/-- The resolvent-weighted test occurring in one ordered off-diagonal term of
the Dyson equation. -/
def coordinateResolventLowerTest
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r s : ℝ) : ℂ :=
  sourceInverse (coordinateMatrix B a b r s) z i j *
    lowerConjugateMomentTest m
      (coordinateSignedError p B a b x y z r s)

/-- Real-coordinate derivative of the resolvent-weighted lower-moment test. -/
def coordinateResolventLowerDerivReal
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r s : ℝ) : ℂ :=
  -(sourceInverse (coordinateMatrix B a b r s) z i a *
      sourceInverse (coordinateMatrix B a b r s) z b j +
    sourceInverse (coordinateMatrix B a b r s) z i b *
      sourceInverse (coordinateMatrix B a b r s) z a j) *
      lowerConjugateMomentTest m
        (coordinateSignedError p B a b x y z r s) +
    sourceInverse (coordinateMatrix B a b r s) z i j *
      lowerConjugateMomentDerivative m
        (coordinateSignedError p B a b x y z r s)
        (coordinateSignedErrorDerivReal p B a b x y z r s)

/-- Imaginary-coordinate derivative of the resolvent-weighted lower-moment
 test. -/
def coordinateResolventLowerDerivImaginary
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r s : ℝ) : ℂ :=
  (-Complex.I * sourceInverse (coordinateMatrix B a b r s) z i a *
      sourceInverse (coordinateMatrix B a b r s) z b j +
    Complex.I * sourceInverse (coordinateMatrix B a b r s) z i b *
      sourceInverse (coordinateMatrix B a b r s) z a j) *
      lowerConjugateMomentTest m
        (coordinateSignedError p B a b x y z r s) +
    sourceInverse (coordinateMatrix B a b r s) z i j *
      lowerConjugateMomentDerivative m
        (coordinateSignedError p B a b x y z r s)
        (coordinateSignedErrorDerivImaginary p B a b x y z r s)

/-- Product rule in the real coordinate: this includes both the derivative of
`Gᵢⱼ` and the derivative of the lower moment. -/
theorem hasDerivAt_coordinateResolventLowerTest_real
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) (r s : ℝ) :
    HasDerivAt
      (fun t => coordinateResolventLowerTest p B a b x y i j z m t s)
      (coordinateResolventLowerDerivReal p B a b x y i j z m r s) r := by
  unfold coordinateResolventLowerTest coordinateResolventLowerDerivReal
  exact (hasDerivAt_sourceInverse_coordinate_real B hB a b i j z hz r s).mul
    (hasDerivAt_lowerConjugateMomentTest m
      (hasDerivAt_coordinateSignedError_real p B hB a b x y z hz r s))

/-- Product rule in the imaginary coordinate. -/
theorem hasDerivAt_coordinateResolventLowerTest_imaginary
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) (r s : ℝ) :
    HasDerivAt
      (fun t => coordinateResolventLowerTest p B a b x y i j z m r t)
      (coordinateResolventLowerDerivImaginary p B a b x y i j z m r s) s := by
  unfold coordinateResolventLowerTest coordinateResolventLowerDerivImaginary
  exact (hasDerivAt_sourceInverse_coordinate_imaginary B hB a b i j z hz r s).mul
    (hasDerivAt_lowerConjugateMomentTest m
      (hasDerivAt_coordinateSignedError_imaginary p B hB a b x y z hz r s))

/-- The circular `r + i s` recombination isolates the orientation in which
the differentiated Green entry runs through `b` and then `a`. -/
theorem coordinateResolventLowerDerivative_circular
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r s : ℝ) :
    coordinateResolventLowerDerivReal p B a b x y i j z m r s +
        Complex.I * coordinateResolventLowerDerivImaginary
          p B a b x y i j z m r s =
      -2 * sourceInverse (coordinateMatrix B a b r s) z i b *
          sourceInverse (coordinateMatrix B a b r s) z a j *
          lowerConjugateMomentTest m
            (coordinateSignedError p B a b x y z r s) +
        sourceInverse (coordinateMatrix B a b r s) z i j *
          (lowerConjugateMomentDerivative m
              (coordinateSignedError p B a b x y z r s)
              (coordinateSignedErrorDerivReal p B a b x y z r s) +
            Complex.I * lowerConjugateMomentDerivative m
              (coordinateSignedError p B a b x y z r s)
              (coordinateSignedErrorDerivImaginary p B a b x y z r s)) := by
  unfold coordinateResolventLowerDerivReal
    coordinateResolventLowerDerivImaginary
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The conjugate circular `r - i s` recombination isolates the reversed
orientation. -/
theorem coordinateResolventLowerDerivative_conjugateCircular
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r s : ℝ) :
    coordinateResolventLowerDerivReal p B a b x y i j z m r s -
        Complex.I * coordinateResolventLowerDerivImaginary
          p B a b x y i j z m r s =
      -2 * sourceInverse (coordinateMatrix B a b r s) z i a *
          sourceInverse (coordinateMatrix B a b r s) z b j *
          lowerConjugateMomentTest m
            (coordinateSignedError p B a b x y z r s) +
        sourceInverse (coordinateMatrix B a b r s) z i j *
          (lowerConjugateMomentDerivative m
              (coordinateSignedError p B a b x y z r s)
              (coordinateSignedErrorDerivReal p B a b x y z r s) -
            Complex.I * lowerConjugateMomentDerivative m
              (coordinateSignedError p B a b x y z r s)
              (coordinateSignedErrorDerivImaginary p B a b x y z r s)) := by
  unfold coordinateResolventLowerDerivReal
    coordinateResolventLowerDerivImaginary
  ring_nf
  rw [Complex.I_sq]
  ring

/-- At the coordinates of a sample, the coordinate resolvent-weighted test is
the ordered Green-entry/lower-moment factor used in the Dyson identity. -/
theorem coordinateResolventLowerTest_actual
    {p : Params} (M : Law p) (a b x y i j : Site p.n p.W)
    (hab : siteLE p a b) (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) (ω : M.Ω) :
    coordinateResolventLowerTest p (offdiagBackground (M.H ω) a b)
        a b x y i j z m (M.H ω a b).re (M.H ω a b).im =
      green M z ω i j *
        lowerConjugateMomentTest m
          (ERFluctuationMoments.signedResolventError M z x y ω) := by
  unfold coordinateResolventLowerTest
  rw [actual_offdiag_coordinate_decomposition]
  rw [sourceInverse_actual M z hz ω]
  rw [coordinateSignedError_actual M ⟨(a, b), hab⟩ x y z hz ω]

/-!
## The separate diagonal real coordinate
-/

/-- Hermitian direction of one diagonal real coordinate. -/
def diagonalRealDirection {ι : Type*} [DecidableEq ι] (a : ι) :
    Matrix ι ι ℂ := Matrix.single a a 1

/-- The diagonal real direction is Hermitian. -/
theorem diagonalRealDirection_isHermitian
    {ι : Type*} [DecidableEq ι] (a : ι) :
    (diagonalRealDirection a).IsHermitian := by
  simp [diagonalRealDirection, Matrix.IsHermitian,
    Matrix.conjTranspose_single]

/-- Remove one real diagonal coordinate from a Hermitian matrix. -/
def diagonalRealBackground {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (a : ι) : Matrix ι ι ℂ :=
  H - (H a a).re • diagonalRealDirection a

/-- Reinsert one real diagonal coordinate. -/
def diagonalRealCoordinateMatrix {ι : Type*} [DecidableEq ι]
    (B : Matrix ι ι ℂ) (a : ι) (r : ℝ) : Matrix ι ι ℂ :=
  B + r • diagonalRealDirection a

/-- Exact diagonal-coordinate reconstruction of a Hermitian matrix. -/
theorem diagonalReal_coordinate_decomposition
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ) (a : ι) :
    diagonalRealCoordinateMatrix (diagonalRealBackground H a) a (H a a).re = H := by
  unfold diagonalRealCoordinateMatrix diagonalRealBackground
  abel

/-- Removing a real diagonal coordinate preserves Hermiticity. -/
theorem diagonalRealBackground_isHermitian
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (a : ι) :
    (diagonalRealBackground H a).IsHermitian := by
  exact hH.sub ((diagonalRealDirection_isHermitian a).smul
    (RCLike.conj_ofReal (H a a).re))

/-- Every diagonal reconstruction from a Hermitian background is Hermitian. -/
theorem diagonalRealCoordinateMatrix_isHermitian
    {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (a : ι) (r : ℝ) :
    (diagonalRealCoordinateMatrix B a r).IsHermitian := by
  exact hB.add ((diagonalRealDirection_isHermitian a).smul
    (RCLike.conj_ofReal r))

/-- Exact inverse derivative in the diagonal real direction. -/
theorem hasDerivAt_sourceInverse_coordinate_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (a i j : ι)
    (z : ℂ) (hz : z.im ≠ 0) (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => sourceInverse (diagonalRealCoordinateMatrix B a t) z i j)
      (-sourceInverse (diagonalRealCoordinateMatrix B a r) z i a *
        sourceInverse (diagonalRealCoordinateMatrix B a r) z a j) r := by
  have h := hasDerivAt_sourceInverse_direction B (diagonalRealDirection a)
    hB (diagonalRealDirection_isHermitian a) z hz i j r
  have hentry :
      (sourceInverse (B + r • diagonalRealDirection a) z *
        diagonalRealDirection a *
        sourceInverse (B + r • diagonalRealDirection a) z) i j =
      sourceInverse (B + r • diagonalRealDirection a) z i a *
    sourceInverse (B + r • diagonalRealDirection a) z a j := by
    rw [Matrix.mul_apply]
    calc
      (∑ b, (sourceInverse (B + r • diagonalRealDirection a) z *
          diagonalRealDirection a) i b *
          sourceInverse (B + r • diagonalRealDirection a) z b j) =
        (sourceInverse (B + r • diagonalRealDirection a) z *
          diagonalRealDirection a) i a *
          sourceInverse (B + r • diagonalRealDirection a) z a j := by
        apply Finset.sum_eq_single a
        · intro b _ hba
          rw [show diagonalRealDirection a = Matrix.single a a 1 by rfl]
          rw [Matrix.mul_single_apply_of_ne (hbj := hba)]
          simp
        · simp
      _ = _ := by
        rw [show diagonalRealDirection a = Matrix.single a a 1 by rfl]
        rw [Matrix.mul_single_apply_same]
        simp
  rw [hentry] at h
  simpa [diagonalRealCoordinateMatrix] using h

/-- Diagonal-coordinate version of the signed covariance-weighted error. -/
def diagonalCoordinateSignedError
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a x y : Site p.n p.W) (z : ℂ) (r : ℝ) : ℂ :=
  ∑ k, (siteCovariance p x k : ℂ) *
    (sourceInverse (diagonalRealCoordinateMatrix B a r) z k y -
      semicircleMatrix p z k y)

/-- Displayed derivative of the diagonal-coordinate signed error. -/
def diagonalCoordinateSignedErrorDeriv
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a x y : Site p.n p.W) (z : ℂ) (r : ℝ) : ℂ :=
  -∑ k, (siteCovariance p x k : ℂ) *
    sourceInverse (diagonalRealCoordinateMatrix B a r) z k a *
    sourceInverse (diagonalRealCoordinateMatrix B a r) z a y

/-- The diagonal signed-error derivative is proved entrywise from the exact
inverse derivative. -/
theorem hasDerivAt_diagonalCoordinateSignedError
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a x y : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (r : ℝ) :
    HasDerivAt (fun t => diagonalCoordinateSignedError p B a x y z t)
      (diagonalCoordinateSignedErrorDeriv p B a x y z r) r := by
  unfold diagonalCoordinateSignedError diagonalCoordinateSignedErrorDeriv
  convert HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_sourceInverse_coordinate_diagonal B hB a k y z hz r).sub_const
      (semicircleMatrix p z k y) |>.const_mul
        (siteCovariance p x k : ℂ)) using 1
  · funext t
    simp only [Finset.sum_apply]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The diagonal Green/lower-moment test whose real Gaussian IBP is separate
from the circular strict-coordinate calculation. -/
def diagonalResolventLowerTest
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r : ℝ) : ℂ :=
  sourceInverse (diagonalRealCoordinateMatrix B a r) z i j *
    lowerConjugateMomentTest m
      (diagonalCoordinateSignedError p B a x y z r)

/-- Full product derivative of the diagonal resolvent-weighted test. -/
def diagonalResolventLowerDerivative
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (r : ℝ) : ℂ :=
  (-sourceInverse (diagonalRealCoordinateMatrix B a r) z i a *
      sourceInverse (diagonalRealCoordinateMatrix B a r) z a j) *
      lowerConjugateMomentTest m
        (diagonalCoordinateSignedError p B a x y z r) +
    sourceInverse (diagonalRealCoordinateMatrix B a r) z i j *
      lowerConjugateMomentDerivative m
        (diagonalCoordinateSignedError p B a x y z r)
        (diagonalCoordinateSignedErrorDeriv p B a x y z r)

/-- The separate diagonal observable has the claimed exact derivative. -/
theorem hasDerivAt_diagonalResolventLowerTest
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) (r : ℝ) :
    HasDerivAt (fun t => diagonalResolventLowerTest p B a x y i j z m t)
      (diagonalResolventLowerDerivative p B a x y i j z m r) r := by
  unfold diagonalResolventLowerTest diagonalResolventLowerDerivative
  exact (hasDerivAt_sourceInverse_coordinate_diagonal B hB a i j z hz r).mul
    (hasDerivAt_lowerConjugateMomentTest m
      (hasDerivAt_diagonalCoordinateSignedError p B hB a x y z hz r))

/-- Substitution of the diagonal coordinate of a sample recovers the signed
fluctuation exactly. -/
theorem diagonalCoordinateSignedError_actual
    {p : Params} (M : Law p) (a x y : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (ω : M.Ω) :
    diagonalCoordinateSignedError p (diagonalRealBackground (M.H ω) a)
        a x y z (M.H ω a a).re =
      ERFluctuationMoments.signedResolventError M z x y ω := by
  unfold diagonalCoordinateSignedError
  rw [diagonalReal_coordinate_decomposition]
  rw [sourceInverse_actual M z hz ω]
  rfl

/-- Substitution of the diagonal coordinate of a sample recovers the precise
Green-entry/lower-moment observable used in the diagonal Dyson term. -/
theorem diagonalResolventLowerTest_actual
    {p : Params} (M : Law p) (a x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) (ω : M.Ω) :
    diagonalResolventLowerTest p (diagonalRealBackground (M.H ω) a)
        a x y i j z m (M.H ω a a).re =
      green M z ω i j * lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) := by
  unfold diagonalResolventLowerTest
  rw [diagonalReal_coordinate_decomposition]
  rw [sourceInverse_actual M z hz ω]
  rw [diagonalCoordinateSignedError_actual M a x y z hz ω]

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
