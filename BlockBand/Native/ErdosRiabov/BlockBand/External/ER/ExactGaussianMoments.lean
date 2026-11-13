module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAdmissibility
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.LocalLawBootstrap
public import Mathlib.Probability.Independence.Integration

/-!
# Exact Gaussian-ring moments and covariance

This module proves the probabilistic content of the Erdős–Riabov covariance
lemma.  Starting from the exact entry laws in
`ERProfile.ExactGaussianRingCovariance`, it derives centering, all finite
`Lᵖ` moments, the real component variances, circular complex second moment,
and squared-norm covariance with the exact `W⁻¹` site normalization.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.1 and Proposition 2.8(ii).  The matrix law is
the cyclic Gaussian-ring law of the paper: diagonal entries are real
centered Gaussians and the real and imaginary parts of each strict upper entry
are independent centered Gaussians of variance `siteCovariance / 2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERExactGaussianMoments

open MeasureTheory ProbabilityTheory
open ERProfile ERLocalLaw

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The Gaussian cumulant sequence: only order two survives. -/
def gaussianCumulantSequence (variance : ℂ) : ℕ → ℂ :=
  fun r => if r = 2 then variance else 0

/-- The displayed sequence has exactly the Gaussian cumulants, with no
higher-order remainder. -/
theorem gaussianCumulantSequence_spec (variance : ℂ) :
    GaussianCumulantSequence variance (gaussianCumulantSequence variance) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [gaussianCumulantSequence]
  · simp [gaussianCumulantSequence]
  · simp [gaussianCumulantSequence]
  · intro r hr
    simp [gaussianCumulantSequence, show r ≠ 2 by omega]

/-- A centered Gaussian real coordinate has mean zero. -/
theorem integral_eq_zero_of_hasLaw_gaussianReal_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {v : NNReal} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ∂P = 0 := by
  rw [(hX.identDistrib HasLaw.id).integral_eq]
  simpa only [id_eq] using
    (integral_id_gaussianReal : ∫ x, x ∂gaussianReal 0 v = 0)

/-- A real coordinate with Gaussian law has every finite `Lᵖ` moment. -/
theorem memLp_of_hasLaw_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ} {v : NNReal} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal μ v) P) (q : NNReal) :
    MemLp X q P := by
  exact (hX.identDistrib HasLaw.id).memLp_iff.mpr
    (by simpa only [id_eq] using
      (memLp_id_gaussianReal (μ := μ) (v := v) q))

/-- The second raw moment of a centered Gaussian coordinate is its variance. -/
theorem integral_sq_eq_of_hasLaw_gaussianReal_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {v : NNReal} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = v := by
  calc
    ∫ ω, X ω ^ 2 ∂P =
        ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v := by
      simpa only [Function.comp_apply] using
        hX.integral_comp ((measurable_id'.pow_const 2).aestronglyMeasurable)
    _ = v := by
      calc
        ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v =
            variance id (gaussianReal 0 v) := by
          rw [variance_eq_integral measurable_id.aemeasurable]
          simp only [integral_id_gaussianReal, sub_zero, id_eq]
        _ = v := variance_id_gaussianReal

/-- Complete moment/covariance package for the exact Gaussian ring.  It is a
consequence of the concrete law, not an analytic input or certificate. -/
structure ExactGaussianRingMoments (p : Params) (M : Law p) : Prop
    extends ExactGaussianRingCovariance p M where
  diagonal_mean_zero : ∀ x, ∫ ω, (M.H ω x x).re ∂M.P = 0
  diagonal_allMoments : ∀ (x : Site p.n p.W) (q : NNReal),
    MemLp (fun ω => (M.H ω x x).re) q M.P
  diagonal_secondMoment : ∀ x,
    ∫ ω, (M.H ω x x).re ^ 2 ∂M.P = siteCovariance p x x
  offdiag_re_mean_zero : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, (M.H ω x y).re ∂M.P = 0
  offdiag_im_mean_zero : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, (M.H ω x y).im ∂M.P = 0
  offdiag_mean_zero : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, M.H ω x y ∂M.P = 0
  offdiag_re_allMoments : ∀ x y, siteLE p x y → x ≠ y → ∀ q : NNReal,
    MemLp (fun ω => (M.H ω x y).re) q M.P
  offdiag_im_allMoments : ∀ x y, siteLE p x y → x ≠ y → ∀ q : NNReal,
    MemLp (fun ω => (M.H ω x y).im) q M.P
  offdiag_allMoments : ∀ x y, siteLE p x y → x ≠ y → ∀ q : NNReal,
    MemLp (fun ω => M.H ω x y) q M.P
  offdiag_re_secondMoment : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, (M.H ω x y).re ^ 2 ∂M.P = siteCovariance p x y / 2
  offdiag_im_secondMoment : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, (M.H ω x y).im ^ 2 ∂M.P = siteCovariance p x y / 2
  offdiag_mixedMoment_zero : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, (M.H ω x y).re * (M.H ω x y).im ∂M.P = 0
  offdiag_complexSecondMoment : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, M.H ω x y ^ 2 ∂M.P = 0
  offdiag_normSqMoment : ∀ x y, siteLE p x y → x ≠ y →
    ∫ ω, ‖M.H ω x y‖ ^ 2 ∂M.P = siteCovariance p x y
  diagonal_cumulants : ∀ x,
    GaussianCumulantSequence (siteCovariance p x x)
      (gaussianCumulantSequence (siteCovariance p x x))
  offdiag_component_cumulants : ∀ x y, siteLE p x y → x ≠ y →
    GaussianCumulantSequence (siteCovariance p x y / 2)
      (gaussianCumulantSequence (siteCovariance p x y / 2))

/-- Every exact Gaussian-ring law has the complete centered moment and covariance
package with the normalization of the paper. -/
theorem exactGaussianRingMoments (p : Params) (M : Law p) :
    ExactGaussianRingMoments p M := by
  let hcov := exactGaussianRingCovariance p M
  refine
    { toExactGaussianRingCovariance := hcov
      diagonal_mean_zero := ?_
      diagonal_allMoments := ?_
      diagonal_secondMoment := ?_
      offdiag_re_mean_zero := ?_
      offdiag_im_mean_zero := ?_
      offdiag_mean_zero := ?_
      offdiag_re_allMoments := ?_
      offdiag_im_allMoments := ?_
      offdiag_allMoments := ?_
      offdiag_re_secondMoment := ?_
      offdiag_im_secondMoment := ?_
      offdiag_mixedMoment_zero := ?_
      offdiag_complexSecondMoment := ?_
      offdiag_normSqMoment := ?_
      diagonal_cumulants := ?_
      offdiag_component_cumulants := ?_ }
  · intro x
    exact integral_eq_zero_of_hasLaw_gaussianReal_zero (hcov.diagonalGaussian x)
  · intro x q
    exact memLp_of_hasLaw_gaussianReal (hcov.diagonalGaussian x) q
  · intro x
    exact integral_sq_eq_of_hasLaw_gaussianReal_zero (hcov.diagonalGaussian x)
  · intro x y hxy hne
    exact integral_eq_zero_of_hasLaw_gaussianReal_zero
      (hcov.offdiagRealGaussian x y hxy hne)
  · intro x y hxy hne
    exact integral_eq_zero_of_hasLaw_gaussianReal_zero
      (hcov.offdiagImagGaussian x y hxy hne)
  · intro x y hxy hne
    have hint : Integrable (fun ω => M.H ω x y) M.P :=
      Integrable.re_im_iff.mp ⟨
        (memLp_of_hasLaw_gaussianReal
          (hcov.offdiagRealGaussian x y hxy hne) 1).integrable (by norm_num),
        (memLp_of_hasLaw_gaussianReal
          (hcov.offdiagImagGaussian x y hxy hne) 1).integrable (by norm_num)⟩
    rw [← integral_re_add_im hint]
    change ((∫ ω, (M.H ω x y).re ∂M.P : ℝ) : ℂ) +
      (∫ ω, (M.H ω x y).im ∂M.P : ℝ) * Complex.I = 0
    rw [
      integral_eq_zero_of_hasLaw_gaussianReal_zero
        (hcov.offdiagRealGaussian x y hxy hne),
      integral_eq_zero_of_hasLaw_gaussianReal_zero
        (hcov.offdiagImagGaussian x y hxy hne)]
    simp
  · intro x y hxy hne q
    exact memLp_of_hasLaw_gaussianReal
      (hcov.offdiagRealGaussian x y hxy hne) q
  · intro x y hxy hne q
    exact memLp_of_hasLaw_gaussianReal
      (hcov.offdiagImagGaussian x y hxy hne) q
  · intro x y hxy hne q
    exact memLp_re_im_iff.mp ⟨
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagRealGaussian x y hxy hne) q,
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagImagGaussian x y hxy hne) q⟩
  · intro x y hxy hne
    exact integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagRealGaussian x y hxy hne)
  · intro x y hxy hne
    exact integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagImagGaussian x y hxy hne)
  · intro x y hxy hne
    rw [(hcov.componentsIndependent x y hxy hne).integral_fun_mul_eq_mul_integral
      (hcov.offdiagRealGaussian x y hxy hne).aemeasurable.aestronglyMeasurable
      (hcov.offdiagImagGaussian x y hxy hne).aemeasurable.aestronglyMeasurable]
    rw [integral_eq_zero_of_hasLaw_gaussianReal_zero
      (hcov.offdiagRealGaussian x y hxy hne),
      integral_eq_zero_of_hasLaw_gaussianReal_zero
      (hcov.offdiagImagGaussian x y hxy hne), zero_mul]
  · intro x y hxy hne
    have hre := integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagRealGaussian x y hxy hne)
    have him := integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagImagGaussian x y hxy hne)
    have hreLp : MemLp (fun ω => (M.H ω x y).re) 2 M.P :=
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagRealGaussian x y hxy hne) 2
    have himLp : MemLp (fun ω => (M.H ω x y).im) 2 M.P :=
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagImagGaussian x y hxy hne) 2
    have hre2 : Integrable (fun ω => (M.H ω x y).re ^ 2) M.P := by
      rw [show (fun ω => (M.H ω x y).re ^ 2) =
          (fun ω => (M.H ω x y).re) * fun ω => (M.H ω x y).re by
        funext ω
        exact pow_two _]
      exact hreLp.integrable_mul hreLp
    have him2 : Integrable (fun ω => (M.H ω x y).im ^ 2) M.P := by
      rw [show (fun ω => (M.H ω x y).im ^ 2) =
          (fun ω => (M.H ω x y).im) * fun ω => (M.H ω x y).im by
        funext ω
        exact pow_two _]
      exact himLp.integrable_mul himLp
    have hmixInt :
        Integrable (fun ω => (M.H ω x y).re * (M.H ω x y).im) M.P :=
      hreLp.integrable_mul himLp
    have hmix :
        ∫ ω, (M.H ω x y).re * (M.H ω x y).im ∂M.P = 0 := by
      rw [(hcov.componentsIndependent x y hxy hne).integral_fun_mul_eq_mul_integral
        (hcov.offdiagRealGaussian x y hxy hne).aemeasurable.aestronglyMeasurable
        (hcov.offdiagImagGaussian x y hxy hne).aemeasurable.aestronglyMeasurable]
      rw [integral_eq_zero_of_hasLaw_gaussianReal_zero
        (hcov.offdiagRealGaussian x y hxy hne),
        integral_eq_zero_of_hasLaw_gaussianReal_zero
        (hcov.offdiagImagGaussian x y hxy hne), zero_mul]
    have hsquareInt : Integrable (fun ω => M.H ω x y ^ 2) M.P := by
      have hdecomp :
          (fun ω => M.H ω x y ^ 2) =
            fun ω => (((M.H ω x y).re ^ 2 - (M.H ω x y).im ^ 2 : ℝ) : ℂ) +
              (2 * ((M.H ω x y).re * (M.H ω x y).im) : ℝ) * Complex.I := by
        funext ω
        apply Complex.ext
        · simp [pow_two]
        · simp [pow_two]
          ring
      rw [hdecomp]
      exact (hre2.sub him2).ofReal.add
        ((hmixInt.const_mul 2).ofReal.mul_const Complex.I)
    rw [show (fun ω => M.H ω x y ^ 2) =
        fun ω => (((M.H ω x y).re ^ 2 - (M.H ω x y).im ^ 2 : ℝ) : ℂ) +
          (2 * ((M.H ω x y).re * (M.H ω x y).im) : ℝ) * Complex.I by
      funext ω
      apply Complex.ext
      · simp [pow_two]
      · simp [pow_two]
        ring]
    rw [integral_add]
    rw [integral_complex_ofReal, integral_sub hre2 him2, hre, him, sub_self]
    change (0 : ℂ) +
      (∫ ω, ((2 * ((M.H ω x y).re * (M.H ω x y).im) : ℝ) : ℂ) *
        Complex.I ∂M.P) = 0
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hmix]
    simp
    · exact (hre2.sub him2).ofReal
    · exact (hmixInt.const_mul 2).ofReal.mul_const Complex.I
  · intro x y hxy hne
    have hre := integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagRealGaussian x y hxy hne)
    have him := integral_sq_eq_of_hasLaw_gaussianReal_zero
      (hcov.offdiagImagGaussian x y hxy hne)
    have hreLp : MemLp (fun ω => (M.H ω x y).re) 2 M.P :=
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagRealGaussian x y hxy hne) 2
    have himLp : MemLp (fun ω => (M.H ω x y).im) 2 M.P :=
      memLp_of_hasLaw_gaussianReal
        (hcov.offdiagImagGaussian x y hxy hne) 2
    have hre2 : Integrable (fun ω => (M.H ω x y).re ^ 2) M.P := by
      rw [show (fun ω => (M.H ω x y).re ^ 2) =
          (fun ω => (M.H ω x y).re) * fun ω => (M.H ω x y).re by
        funext ω
        exact pow_two _]
      exact hreLp.integrable_mul hreLp
    have him2 : Integrable (fun ω => (M.H ω x y).im ^ 2) M.P := by
      rw [show (fun ω => (M.H ω x y).im ^ 2) =
          (fun ω => (M.H ω x y).im) * fun ω => (M.H ω x y).im by
        funext ω
        exact pow_two _]
      exact himLp.integrable_mul himLp
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    rw [integral_add]
    · rw [show (fun ω => (M.H ω x y).re * (M.H ω x y).re) =
          fun ω => (M.H ω x y).re ^ 2 by funext ω; ring,
        show (fun ω => (M.H ω x y).im * (M.H ω x y).im) =
          fun ω => (M.H ω x y).im ^ 2 by funext ω; ring,
        hre, him]
      change (siteCovariance p x y / 2 : ℝ) +
          siteCovariance p x y / 2 = siteCovariance p x y
      ring
    · simpa only [pow_two] using hre2
    · simpa only [pow_two] using him2
  · intro x
    exact gaussianCumulantSequence_spec _
  · intro x y hxy hne
    exact gaussianCumulantSequence_spec _

end ERExactGaussianMoments
end GaussianRing
end ERNative.BlockBand
