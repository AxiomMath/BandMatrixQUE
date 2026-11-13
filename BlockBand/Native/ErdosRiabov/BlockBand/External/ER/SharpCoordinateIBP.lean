module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ResolventMomentIBP
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Sharp coordinate IBP for the Gaussian-ring fluctuation

This file proves the analytic facts which precede the sharp ER Ward
contraction.  It proves the inverse derivative entry by entry, and keeps the
complementary Hermitian background as a separate factor in the product law.  Bounds below
are uniform over that background and therefore supply measurable domination for Gaussian
Fubini and both real coordinate integrations by parts.

No local-law estimate, stochastic-domination hypothesis, or all-order moment assumption is
used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERActualWardBound
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Evaluation of one matrix entry as a continuous real-linear map. -/
def entryCLM {ι : Type*} [Fintype ι] (i j : ι) :
    Matrix ι ι ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => (ι → ℂ)) i)

/-- Exact real derivative of the source-sign inverse along an arbitrary
Hermitian direction.  Pole exclusion follows from Hermiticity and `Im z ≠ 0`. -/
theorem hasDerivAt_sourceInverse_direction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => sourceInverse (A + t • D) z i j)
      (-(sourceInverse (A + r • D) z * D *
        sourceInverse (A + r • D) z) i j) r := by
  let P : ℂ → Matrix ι ι ℂ := fun t => A + t • D - z • (1 : Matrix ι ι ℂ)
  have hHerm (t : ℝ) : (A + t • D).IsHermitian :=
    hA.add (hD.smul (RCLike.conj_ofReal t))
  have hP (t : ℝ) : IsUnit (P t) := by
    have hu := isUnit_resolventPencil (A + t • D) (hHerm t) hz
    have hneg : -(z • (1 : Matrix ι ι ℂ) - (A + t • D)) = P t := by
      simp [P]
    rw [← hneg]
    exact (IsUnit.neg_iff _).mpr hu
  have hp0 := (((hasDerivAt_id (r : ℂ)).smul_const D).const_add A).sub_const
    (z • (1 : Matrix ι ι ℂ))
  have hp : HasDerivAt P D (r : ℂ) := by
    convert hp0 using 1 <;> simp [P]
  have hPr : P (r : ℂ) = A + r • D - z • (1 : Matrix ι ι ℂ) := by
    ext u v
    simp [P, Complex.real_smul]
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℂ) (hP r).unit).comp_hasDerivAt (r : ℂ) hp
  have huinv : (↑((hP r).unit⁻¹) : Matrix ι ι ℂ) =
      sourceInverse (A + r • D) z := by
    rw [← Ring.inverse_of_isUnit (hP r)]
    rw [sourceInverse, Matrix.nonsing_inv_eq_ringInverse, hPr]
  have hinv : HasDerivAt
      (fun t : ℂ => Ring.inverse (P t))
      (-(sourceInverse (A + r • D) z * D *
        sourceInverse (A + r • D) z)) (r : ℂ) := by
    simpa only [Function.comp_apply, huinv,
      _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, P]
      using! hi
  have hent : HasDerivAt
      (fun t : ℂ => entryCLM i j (Ring.inverse (P t)))
      (entryCLM i j (-(sourceInverse (A + r • D) z * D *
        sourceInverse (A + r • D) z))) (r : ℂ) := by
    simpa only [Function.comp_apply] using!
      ((entryCLM i j).hasFDerivAt.comp_hasDerivAt (r : ℂ) hinv)
  have hreal := hent.comp_ofReal
  simpa only [entryCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, sourceInverse,
    Matrix.nonsing_inv_eq_ringInverse, P] using! hreal

/-- Affine form of the real coordinate line. -/
theorem coordinateMatrix_realLine
    {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ) (a b : ι) (t s : ℝ) :
    coordinateMatrix B a b t s =
      coordinateMatrix B a b 0 s + t • realDirection a b := by
  simp [coordinateMatrix]
  abel

/-- Affine form of the imaginary coordinate line. -/
theorem coordinateMatrix_imaginaryLine
    {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ) (a b : ι) (r t : ℝ) :
    coordinateMatrix B a b r t =
      coordinateMatrix B a b r 0 + t • imaginaryDirection a b := by
  simp [coordinateMatrix]

/-- Entrywise derivative in the real strict-coordinate direction. -/
theorem hasDerivAt_sourceInverse_coordinate_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (a b i j : ι)
    (z : ℂ) (hz : z.im ≠ 0) (r s : ℝ) :
    HasDerivAt
      (fun t : ℝ => sourceInverse (coordinateMatrix B a b t s) z i j)
      (-(sourceInverse (coordinateMatrix B a b r s) z i a *
          sourceInverse (coordinateMatrix B a b r s) z b j +
        sourceInverse (coordinateMatrix B a b r s) z i b *
          sourceInverse (coordinateMatrix B a b r s) z a j)) r := by
  have h := hasDerivAt_sourceInverse_direction
    (coordinateMatrix B a b 0 s) (realDirection a b)
    (coordinateMatrix_isHermitian B hB a b 0 s)
    (realDirection_isHermitian a b) z hz i j r
  rw [mul_realDirection_mul_apply] at h
  simpa only [← coordinateMatrix_realLine] using h

/-- Entrywise derivative in the imaginary strict-coordinate direction. -/
theorem hasDerivAt_sourceInverse_coordinate_imaginary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (a b i j : ι)
    (z : ℂ) (hz : z.im ≠ 0) (r s : ℝ) :
    HasDerivAt
      (fun t : ℝ => sourceInverse (coordinateMatrix B a b r t) z i j)
      (-Complex.I * sourceInverse (coordinateMatrix B a b r s) z i a *
          sourceInverse (coordinateMatrix B a b r s) z b j +
        Complex.I * sourceInverse (coordinateMatrix B a b r s) z i b *
          sourceInverse (coordinateMatrix B a b r s) z a j) s := by
  have h := hasDerivAt_sourceInverse_direction
    (coordinateMatrix B a b r 0) (imaginaryDirection a b)
    (coordinateMatrix_isHermitian B hB a b r 0)
    (imaginaryDirection_isHermitian a b) z hz i j s
  rw [mul_imaginaryDirection_mul_apply] at h
  simp only [← coordinateMatrix_imaginaryLine] at h
  convert h using 1; ring

/-- The real-coordinate derivative of the covariance-weighted signed error is
`coordinateSignedErrorDerivReal` (a `HasDerivAt` statement), obtained by summing the exact
inverse derivatives. -/
theorem hasDerivAt_coordinateSignedError_real
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (r s : ℝ) :
    HasDerivAt (fun t => coordinateSignedError p B a b x y z t s)
      (coordinateSignedErrorDerivReal p B a b x y z r s) r := by
  unfold coordinateSignedError coordinateSignedErrorDerivReal
  convert HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_sourceInverse_coordinate_real B hB a b k y z hz r s).sub_const
      (ERConcrete.semicircleMatrix p z k y) |>.const_mul
        (ERProfile.siteCovariance p x k : ℂ)) using 1
  · funext t
    simp only [Finset.sum_apply]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Imaginary-coordinate counterpart of
`hasDerivAt_coordinateSignedError_real`. -/
theorem hasDerivAt_coordinateSignedError_imaginary
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (r s : ℝ) :
    HasDerivAt (fun t => coordinateSignedError p B a b x y z r t)
      (coordinateSignedErrorDerivImaginary p B a b x y z r s) s := by
  unfold coordinateSignedError coordinateSignedErrorDerivImaginary
  convert HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_sourceInverse_coordinate_imaginary B hB a b k y z hz r s).sub_const
      (ERConcrete.semicircleMatrix p z k y) |>.const_mul
        (ERProfile.siteCovariance p x k : ℂ)) using 1
  · funext t
    simp only [Finset.sum_apply]

/-!
## Uniform domination over every Hermitian complementary background
-/

/-- The source-sign inverse and the resolvent `matrixResolvent` differ by exactly one minus
sign. -/
theorem sourceInverse_eq_neg_matrixResolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    sourceInverse A z = -matrixResolvent A z := by
  let Q := z • (1 : Matrix ι ι ℂ) - A
  have hQ : IsUnit Q := isUnit_resolventPencil A hA hz
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  unfold sourceInverse
  apply Matrix.inv_eq_right_inv
  have hmul := Matrix.mul_nonsing_inv Q hdet
  change (A - z • (1 : Matrix ι ι ℂ)) * (-Q⁻¹) = 1
  rw [show A - z • (1 : Matrix ι ι ℂ) = -Q by simp [Q]]
  simpa using hmul

/-- Every coordinate inverse entry is uniformly bounded over both real
coordinates and over every Hermitian complementary background. -/
theorem norm_sourceInverse_coordinate_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (a b i j : ι)
    (z : ℂ) (hz : 0 < z.im) (r s : ℝ) :
    ‖sourceInverse (coordinateMatrix B a b r s) z i j‖ ≤ (z.im)⁻¹ := by
  rw [sourceInverse_eq_neg_matrixResolvent _
    (coordinateMatrix_isHermitian B hB a b r s) z hz.ne']
  simpa using norm_matrixResolvent_entry_le
    (coordinateMatrix B a b r s)
    (coordinateMatrix_isHermitian B hB a b r s) hz i j

/-- Uniform deterministic bound for the conditioned signed fluctuation. -/
theorem norm_coordinateSignedError_le
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (r s : ℝ) :
    ‖coordinateSignedError p B a b x y z r s‖ ≤
      (z.im)⁻¹ + ‖erSemicircleStieltjes z‖ := by
  rw [coordinateSignedError]
  calc
    ‖∑ k, (siteCovariance p x k : ℂ) *
        (sourceInverse (coordinateMatrix B a b r s) z k y -
          ERConcrete.semicircleMatrix p z k y)‖
      ≤ ∑ k, ‖(siteCovariance p x k : ℂ) *
        (sourceInverse (coordinateMatrix B a b r s) z k y -
          ERConcrete.semicircleMatrix p z k y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, siteCovariance p x k *
        ((z.im)⁻¹ + ‖erSemicircleStieltjes z‖) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (siteCovariance_flat p x k).1]
      apply mul_le_mul_of_nonneg_left _ (siteCovariance_flat p x k).1
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact norm_sourceInverse_coordinate_le B hB a b k y z hz r s
      · by_cases h : k = y <;> simp [ERConcrete.semicircleMatrix, h]
    _ = (z.im)⁻¹ + ‖erSemicircleStieltjes z‖ := by
      rw [← Finset.sum_mul, siteCovariance_stochastic]
      simp

/-- Both exact coordinate derivatives are uniformly bounded by twice the
squared inverse height, independently of the background and the coordinates. -/
theorem norm_coordinateSignedErrorDerivReal_le
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (r s : ℝ) :
    ‖coordinateSignedErrorDerivReal p B a b x y z r s‖ ≤
      2 * (z.im)⁻¹ ^ 2 := by
  rw [coordinateSignedErrorDerivReal, norm_neg]
  calc
    ‖∑ k, (siteCovariance p x k : ℂ) *
      (sourceInverse (coordinateMatrix B a b r s) z k a *
          sourceInverse (coordinateMatrix B a b r s) z b y +
       sourceInverse (coordinateMatrix B a b r s) z k b *
          sourceInverse (coordinateMatrix B a b r s) z a y)‖
      ≤ ∑ k, ‖(siteCovariance p x k : ℂ) *
        (sourceInverse (coordinateMatrix B a b r s) z k a *
            sourceInverse (coordinateMatrix B a b r s) z b y +
         sourceInverse (coordinateMatrix B a b r s) z k b *
            sourceInverse (coordinateMatrix B a b r s) z a y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, siteCovariance p x k * (2 * (z.im)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (siteCovariance_flat p x k).1]
      apply mul_le_mul_of_nonneg_left _ (siteCovariance_flat p x k).1
      calc
        ‖sourceInverse (coordinateMatrix B a b r s) z k a *
            sourceInverse (coordinateMatrix B a b r s) z b y +
          sourceInverse (coordinateMatrix B a b r s) z k b *
            sourceInverse (coordinateMatrix B a b r s) z a y‖
          ≤ ‖sourceInverse (coordinateMatrix B a b r s) z k a‖ *
              ‖sourceInverse (coordinateMatrix B a b r s) z b y‖ +
            ‖sourceInverse (coordinateMatrix B a b r s) z k b‖ *
              ‖sourceInverse (coordinateMatrix B a b r s) z a y‖ := by
                simpa [norm_mul] using norm_add_le
                  (sourceInverse (coordinateMatrix B a b r s) z k a *
                    sourceInverse (coordinateMatrix B a b r s) z b y)
                  (sourceInverse (coordinateMatrix B a b r s) z k b *
                    sourceInverse (coordinateMatrix B a b r s) z a y)
        _ ≤ (z.im)⁻¹ * (z.im)⁻¹ + (z.im)⁻¹ * (z.im)⁻¹ := by
          gcongr <;> exact norm_sourceInverse_coordinate_le B hB a b _ _ z hz r s
        _ = 2 * (z.im)⁻¹ ^ 2 := by ring
    _ = 2 * (z.im)⁻¹ ^ 2 := by
      rw [← Finset.sum_mul, siteCovariance_stochastic]
      simp

/-- The imaginary derivative has the same uniform domination. -/
theorem norm_coordinateSignedErrorDerivImaginary_le
    (p : Params) (B : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hB : B.IsHermitian) (a b x y : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (r s : ℝ) :
    ‖coordinateSignedErrorDerivImaginary p B a b x y z r s‖ ≤
      2 * (z.im)⁻¹ ^ 2 := by
  rw [coordinateSignedErrorDerivImaginary]
  calc
    ‖∑ k, (siteCovariance p x k : ℂ) *
      (-Complex.I * sourceInverse (coordinateMatrix B a b r s) z k a *
          sourceInverse (coordinateMatrix B a b r s) z b y +
       Complex.I * sourceInverse (coordinateMatrix B a b r s) z k b *
          sourceInverse (coordinateMatrix B a b r s) z a y)‖
      ≤ ∑ k, ‖(siteCovariance p x k : ℂ) *
        (-Complex.I * sourceInverse (coordinateMatrix B a b r s) z k a *
            sourceInverse (coordinateMatrix B a b r s) z b y +
         Complex.I * sourceInverse (coordinateMatrix B a b r s) z k b *
            sourceInverse (coordinateMatrix B a b r s) z a y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, siteCovariance p x k * (2 * (z.im)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (siteCovariance_flat p x k).1]
      apply mul_le_mul_of_nonneg_left _ (siteCovariance_flat p x k).1
      calc
        ‖-Complex.I * sourceInverse (coordinateMatrix B a b r s) z k a *
            sourceInverse (coordinateMatrix B a b r s) z b y +
          Complex.I * sourceInverse (coordinateMatrix B a b r s) z k b *
            sourceInverse (coordinateMatrix B a b r s) z a y‖
          ≤ ‖-Complex.I * sourceInverse (coordinateMatrix B a b r s) z k a *
              sourceInverse (coordinateMatrix B a b r s) z b y‖ +
            ‖Complex.I * sourceInverse (coordinateMatrix B a b r s) z k b *
              sourceInverse (coordinateMatrix B a b r s) z a y‖ := norm_add_le _ _
        _ ≤ (z.im)⁻¹ * (z.im)⁻¹ + (z.im)⁻¹ * (z.im)⁻¹ := by
          simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
          gcongr <;> exact norm_sourceInverse_coordinate_le B hB a b _ _ z hz r s
        _ = 2 * (z.im)⁻¹ ^ 2 := by ring
    _ = 2 * (z.im)⁻¹ ^ 2 := by
      rw [← Finset.sum_mul, siteCovariance_stochastic]
      simp

/-!
## Measurable Gaussian domination and the two one-dimensional IBPs
-/

/-- Every coordinate is split into the zero-variance Dirac case or
the supported positive-variance case used by the two IBPs. -/
theorem siteCovariance_zero_or_positive
    (p : Params) (a b : Site p.n p.W) :
    siteCovariance p a b = 0 ∨ 0 < siteCovariance p a b := by
  rcases eq_or_lt_of_le (siteCovariance_flat p a b).1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
