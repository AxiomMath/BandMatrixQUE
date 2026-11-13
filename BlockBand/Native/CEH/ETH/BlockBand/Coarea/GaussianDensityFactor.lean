module

public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.GUENormalizer
public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.ProjectiveChartIntegral
public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.GaussianRegression

/-!
# Gaussian density factor in eigenpair coordinates

This module isolates the exact scalar algebra in Claim 2 of the coarea theorem.  With normalized projective Haar measure, the projective
Jacobian constant combines with the consecutive GUE normalizer ratio to give
`c_{d,t}`.  The same file records the pointwise exponential splitting supplied by
the canonical Gaussian-regression identity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Matrix

/-- The density constant `c_{d,t}` of the coarea regression identity.

Normalization: `d` is the complex dimension of the exposed Hermitian block,
`t` is the diagonal (and total off-diagonal complex) GUE variance, and projective
Haar measure has total mass one.  Positivity hypotheses are imposed by the
identities consuming this definition. -/
def coareaGaussianDensityConstant (d : ℕ) (t : ℝ) : ℝ :=
  1 / (((d - 1).factorial : ℝ) * t ^ (d - 1) *
    Real.sqrt (2 * Real.pi * t))

/-- Claim 2's exact normalizer cancellation:
`π^(d-1)/(d-1)! · Z_{d-1}(t)/Z_d(t) = c_{d,t}`.

Source: proof of Claim 2 in the coarea theorem.  The assumptions
`0 < d` and `0 < t` are precisely the nonempty block and positive-variance
hypotheses; there is no limiting or asymptotic parameter. -/
theorem projectiveJacobian_mul_gueNormalizerRatio
    {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    (Real.pi ^ (d - 1) / (d - 1).factorial) *
        (gueNormalizer (d - 1) t / gueNormalizer d t) =
      coareaGaussianDensityConstant d t := by
  rw [gueNormalizer_pred_div (Nat.one_le_iff_ne_zero.mpr hd.ne') ht]
  rw [← Real.sqrt_eq_rpow, Real.rpow_natCast, mul_pow]
  unfold coareaGaussianDensityConstant
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht0 : t ≠ 0 := ht.ne'
  have hfac : ((d - 1).factorial : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  field_simp

/-- The preceding scalar cancellation with the projective Jacobian constant
replaced by its exact affine-chart integral.  This is the positive chart-dimension
case `1 < d`; the algebraic Claim-2 identity above also covers `d = 1`. -/
theorem projectiveChartIntegral_mul_gueNormalizerRatio
    {d : ℕ} (hd : 1 < d) {t : ℝ} (ht : 0 < t) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ d) *
        (gueNormalizer (d - 1) t / gueNormalizer d t) =
      coareaGaussianDensityConstant d t := by
  rw [eigenpairProjectiveChartNormalization d hd]
  exact projectiveJacobian_mul_gueNormalizerRatio (by omega) ht

/-- The non-complementary part of the Gaussian exponent in canonical eigenpair
coordinates.  Here `f = vᴴFv` and `q = (I-vvᴴ)Fv` after sending the selected
unit vector `v` to the first coordinate. -/
def canonicalGaussianRegressionFactor
    {n : Type*} [Fintype n]
    (E f t : ℝ) (q : n → ℂ) : ℝ :=
  Real.exp (-((E - f) ^ 2 + 2 * complexColumnNormSq q) / (2 * t))

/-- Exact exponential form of the Gaussian regression separation in Claim 2.

The selected direction is the first `Unit` coordinate, `q` is the perpendicular
column, and `Fv` is the compression to its complement.  For positive variance
`t`, the full `d`-dimensional GUE exponential is the regression factor
times the complementary `(d-1)`-dimensional GUE exponential. -/
theorem canonicalGaussianExponentialFactorization
    {n : Type*} [Fintype n] [DecidableEq n]
    (E f : ℝ) (q : n → ℂ) (B Fv : Matrix n n ℂ)
    {t : ℝ} (ht : 0 < t) :
    Real.exp
        (-hilbertSchmidtNormSq
          (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B -
            Matrix.fromBlocks ((f : ℂ) • (1 : Matrix Unit Unit ℂ))
              (eigenpairTangentColumn q)ᴴ (eigenpairTangentColumn q) Fv) /
          (2 * t)) =
      canonicalGaussianRegressionFactor E f t q *
        Real.exp (-hilbertSchmidtNormSq (B - Fv) / (2 * t)) := by
  rw [canonicalGaussianRegression E f q B Fv]
  unfold canonicalGaussianRegressionFactor
  rw [← Real.exp_add]
  congr 1
  field_simp [ht.ne']
  ring

end CEHNative.BlockBand
