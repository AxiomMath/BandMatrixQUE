module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ComplementBackgroundReconstruction
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugate-aware moment tests for the ER coordinate expansion

This module supplies the real-coordinate calculus which is needed when
Gaussian integration by parts is applied to a complex resolvent
fluctuation: the signed error on the reconstructed coordinate matrix
(`coordinateSignedError`), its identification with the ER fluctuation
(`coordinateSignedError_actual`), and its real and imaginary coordinate derivatives.

No stochastic estimate or local law is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERResolventMomentIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERStrictCoordinateDisintegration
open ERComplementBackgroundReconstruction
open ERConcrete ERProfile
open scoped BigOperators

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
## The coordinate fluctuation and its differentiated factors
-/

/-- Signed covariance-weighted resolvent error evaluated on the reconstructed
coordinate matrix.  At the selected coordinates of a sample this is definitionally
the random variable from `FluctuationMoments`, after the reconstruction
identity. -/
def coordinateSignedError (p : Params)
    (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y : Site p.n p.W) (z : ℂ) (r s : ℝ) : ℂ :=
  ∑ k, (siteCovariance p x k : ℂ) *
    (sourceInverse (coordinateMatrix B a b r s) z k y -
      semicircleMatrix p z k y)

/-- At a nonreal spectral parameter the source-sign inverse is exactly the
Green-function convention used by the concrete ER fluctuation. -/
theorem sourceInverse_actual
    {p : Params} (M : Law p) (z : ℂ) (hz : z.im ≠ 0) (ω : M.Ω) :
    sourceInverse (M.H ω) z = green M z ω := by
  unfold sourceInverse
  exact Matrix.inv_eq_right_inv (matrix_mul_green M z hz ω)

/-- Substituting the selected coordinates of a sample and the reconstructed
background gives the signed ER fluctuation `weightedFluctuation`. -/
theorem coordinateSignedError_actual
    {p : Params} (M : Law p) (q : UpperPair p)
    (x y : Site p.n p.W) (z : ℂ) (hz : z.im ≠ 0) (ω : M.Ω) :
    coordinateSignedError p
      (offdiagBackground (M.H ω) q.1.1 q.1.2)
      q.1.1 q.1.2 x y z
      (M.H ω q.1.1 q.1.2).re (M.H ω q.1.1 q.1.2).im =
      ERFluctuationMoments.signedResolventError M z x y ω := by
  rw [coordinateSignedError, actual_offdiag_coordinate_decomposition]
  rw [sourceInverse_actual M z hz ω]
  rfl

/-- Real-coordinate derivative produced by the inverse identity
`D G = -G (E_ab+E_ba) G`. -/
def coordinateSignedErrorDerivReal (p : Params)
    (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y : Site p.n p.W) (z : ℂ) (r s : ℝ) : ℂ :=
  -∑ k, (siteCovariance p x k : ℂ) *
    (sourceInverse (coordinateMatrix B a b r s) z k a *
        sourceInverse (coordinateMatrix B a b r s) z b y +
      sourceInverse (coordinateMatrix B a b r s) z k b *
        sourceInverse (coordinateMatrix B a b r s) z a y)

/-- Imaginary-coordinate derivative, retaining the signs which later cancel
the transpose contraction after the two real IBP identities are recombined. -/
def coordinateSignedErrorDerivImaginary (p : Params)
    (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (a b x y : Site p.n p.W) (z : ℂ) (r s : ℝ) : ℂ :=
  ∑ k, (siteCovariance p x k : ℂ) *
    (-Complex.I *
        sourceInverse (coordinateMatrix B a b r s) z k a *
        sourceInverse (coordinateMatrix B a b r s) z b y +
      Complex.I *
        sourceInverse (coordinateMatrix B a b r s) z k b *
        sourceInverse (coordinateMatrix B a b r s) z a y)

end ERResolventMomentIBP
end GaussianRing
end ERNative.BlockBand
