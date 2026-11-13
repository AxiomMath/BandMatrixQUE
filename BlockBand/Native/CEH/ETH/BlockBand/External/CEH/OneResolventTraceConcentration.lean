module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedWardGradient
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Centered one-resolvent trace concentration checkpoint

This module records the strongest consequence of the completed Gaussian
Poincaré calculation that does not use the CEH MDE stability/bootstrap.  The
controlled quantity is the normalized resolvent trace centered by its own
finite-dimensional expectation.  It is not the CEH Theorem 2.3 error
`⟨G-M⟩`, and the polynomial Chebyshev tail below is not called a local law.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ENNReal

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

/-- Pre-MDE stochastic-control quantity associated with CEH Theorem 2.3:
the normalized one-resolvent trace minus its own finite-dimensional expectation
under the transported replicated GUE law.  This uses no spectral-domain
uniformity or large-dimension limit. -/
def centeredOneResolventTrace {N : ℕ} (d : ℕ) (f : Spectrum N)
    (lambda : ℝ) (z : ℂ) (x : CoordinateEuclideanSpace N d) : ℂ :=
  oneResolventTrace d f lambda z x -
    ∫ y, oneResolventTrace d f lambda z y ∂measure N d

/-- The Euclidean one-resolvent trace is Borel measurable. -/
theorem measurable_oneResolventTrace {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Measurable (oneResolventTrace d f lambda z) :=
  (contDiff_oneResolventTrace f lambda hz).continuous.measurable

/-- The centered complex trace is Borel measurable. -/
theorem measurable_centeredOneResolventTrace {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Measurable (centeredOneResolventTrace d f lambda z) := by
  exact (measurable_oneResolventTrace f lambda hz).sub measurable_const

/-- The transported resolvent trace retains the dimension-free resolvent
bound. -/
theorem norm_oneResolventTrace_le {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordinateEuclideanSpace N d) :
    ‖oneResolventTrace d f lambda z x‖ ≤ |z.im|⁻¹ := by
  simpa [oneResolventTrace] using
    norm_replicatedOneResolventTrace_le hN hd f lambda hz
      ((coordinatesEquiv N d).symm x)

/-- The one-resolvent trace is Bochner integrable under the Euclidean GUE law. -/
theorem integrable_oneResolventTrace {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (oneResolventTrace d f lambda z) (measure N d) := by
  apply Integrable.of_bound
    (measurable_oneResolventTrace f lambda hz).aestronglyMeasurable
    |z.im|⁻¹
  exact ae_of_all _ (norm_oneResolventTrace_le hN hd f lambda hz)

/-- The centered trace has the deterministic bound `2 |Im z|⁻¹`. -/
theorem norm_centeredOneResolventTrace_le {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (f : Spectrum N) (lambda : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (x : CoordinateEuclideanSpace N d) :
    ‖centeredOneResolventTrace d f lambda z x‖ ≤ 2 * |z.im|⁻¹ := by
  unfold centeredOneResolventTrace
  calc
    _ ≤ ‖oneResolventTrace d f lambda z x‖ +
        ‖∫ y, oneResolventTrace d f lambda z y ∂measure N d‖ := norm_sub_le _ _
    _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add
      (norm_oneResolventTrace_le hN hd f lambda hz x)
      (by
        simpa using norm_integral_le_of_norm_le_const (μ := measure N d)
          (ae_of_all _ (norm_oneResolventTrace_le hN hd f lambda hz)))
    _ = 2 * |z.im|⁻¹ := by ring

/-- The squared norm of the centered trace is integrable, needed for the
source-faithful Chebyshev tail statement. -/
theorem integrable_norm_sq_centeredOneResolventTrace
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x : CoordinateEuclideanSpace N d =>
      ‖centeredOneResolventTrace d f lambda z x‖ ^ 2) (measure N d) := by
  apply Integrable.of_bound
    ((measurable_centeredOneResolventTrace f lambda hz).norm.pow_const 2).aestronglyMeasurable
    (4 * |z.im|⁻¹ ^ 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_centeredOneResolventTrace_le hN hd f lambda hz x
  calc
    ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 ≤
        (2 * |z.im|⁻¹) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (abs_nonneg _)))).2 h
    _ = 4 * |z.im|⁻¹ ^ 2 := by ring

/-- Exact recombination: the centered complex second moment is the sum of the
real and imaginary variances. -/
theorem integral_norm_sq_centeredOneResolventTrace_eq_variance_add
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ x, ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 ∂measure N d) =
      Var[(fun x : CoordinateEuclideanSpace N d =>
          (oneResolventTrace d f lambda z x).re); measure N d] +
      Var[(fun x : CoordinateEuclideanSpace N d =>
          (oneResolventTrace d f lambda z x).im); measure N d] := by
  let g := oneResolventTrace d f lambda z
  have hg : Integrable g (measure N d) :=
    integrable_oneResolventTrace hN hd f lambda hz
  have hgre : AEMeasurable (fun x => (g x).re) (measure N d) :=
    hg.re.aemeasurable
  have hgim : AEMeasurable (fun x => (g x).im) (measure N d) :=
    hg.im.aemeasurable
  have hcint := integrable_norm_sq_centeredOneResolventTrace hN hd f lambda hz
  have hreint : Integrable (fun x =>
      ((g x).re - ∫ y, (g y).re ∂measure N d) ^ 2) (measure N d) := by
    apply hcint.mono
    · exact ((hgre.sub aemeasurable_const).pow_const 2).aestronglyMeasurable
    · filter_upwards with x
      dsimp [g]
      have hbase : ((oneResolventTrace d f lambda z x).re -
          ∫ y, (oneResolventTrace d f lambda z y).re ∂measure N d) ^ 2 ≤
          ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 := by
        have hre := integral_re hg
        dsimp [g] at hre
        rw [hre]
        change (centeredOneResolventTrace d f lambda z x).re ^ 2 ≤
          ‖centeredOneResolventTrace d f lambda z x‖ ^ 2
        rw [Complex.sq_norm]
        simpa [pow_two] using
          Complex.re_sq_le_normSq (centeredOneResolventTrace d f lambda z x)
      have hl : 0 ≤ ((oneResolventTrace d f lambda z x).re -
          ∫ y, (oneResolventTrace d f lambda z y).re ∂measure N d) ^ 2 := sq_nonneg _
      have hr : 0 ≤ ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 := sq_nonneg _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr] using
        hbase
  have himint : Integrable (fun x =>
      ((g x).im - ∫ y, (g y).im ∂measure N d) ^ 2) (measure N d) := by
    apply hcint.mono
    · exact ((hgim.sub aemeasurable_const).pow_const 2).aestronglyMeasurable
    · filter_upwards with x
      dsimp [g]
      have hbase : ((oneResolventTrace d f lambda z x).im -
          ∫ y, (oneResolventTrace d f lambda z y).im ∂measure N d) ^ 2 ≤
          ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 := by
        have him := integral_im hg
        dsimp [g] at him
        rw [him]
        change (centeredOneResolventTrace d f lambda z x).im ^ 2 ≤
          ‖centeredOneResolventTrace d f lambda z x‖ ^ 2
        rw [Complex.sq_norm]
        simpa [pow_two] using
          Complex.im_sq_le_normSq (centeredOneResolventTrace d f lambda z x)
      have hl : 0 ≤ ((oneResolventTrace d f lambda z x).im -
          ∫ y, (oneResolventTrace d f lambda z y).im ∂measure N d) ^ 2 := sq_nonneg _
      have hr : 0 ≤ ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 := sq_nonneg _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr] using
        hbase
  rw [variance_eq_integral hgre, variance_eq_integral hgim,
    ← integral_add hreint himint]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, centeredOneResolventTrace, g,
    Complex.sub_re, Complex.sub_im]
  have hre := integral_re hg
  have him := integral_im hg
  dsimp [g] at hre him
  rw [← hre, ← him]
  ring

/-- The sharp centered complex second-moment checkpoint obtained by adding the
real and imaginary Poincaré bounds.  It is pointwise in `N`, `d`, and `z`; no
spectral-domain supremum or limit order is asserted. -/
theorem integral_norm_sq_centeredOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ x, ‖centeredOneResolventTrace d f lambda z x‖ ^ 2 ∂measure N d) ≤
      (Real.pi ^ 2 / 2) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
  rw [integral_norm_sq_centeredOneResolventTrace_eq_variance_add hN hd f lambda hz]
  calc
    _ ≤ (Real.pi ^ 2 / 4) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 +
        (Real.pi ^ 2 / 4) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 :=
      add_le_add (variance_oneResolventTrace_re_le hN hd f lambda hz)
        (variance_oneResolventTrace_im_le hN hd f lambda hz)
    _ = _ := by ring

/-- Pointwise Chebyshev consequence of the centered second moment.  For fixed
`N`, `d`, `z`, and threshold `ε`, this is a polynomial tail around the
finite-dimensional expectation, not the CEH local law around the deterministic
MDE solution; it asserts neither domain-uniform stochastic domination nor a
limit order. -/
theorem measureReal_norm_centeredOneResolventTrace_ge_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    (measure N d).real {x | ε ≤ ‖centeredOneResolventTrace d f lambda z x‖} ≤
      ((Real.pi ^ 2 / 2) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) / ε ^ 2 := by
  let q := fun x : CoordinateEuclideanSpace N d =>
    ‖centeredOneResolventTrace d f lambda z x‖ ^ 2
  have hint : Integrable q (measure N d) :=
    integrable_norm_sq_centeredOneResolventTrace hN hd f lambda hz
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := measure N d) (f := q)
    (ae_of_all _ fun x => sq_nonneg _) hint (ε ^ 2)
  have hset : {x | ε ^ 2 ≤ q x} =
      {x | ε ≤ ‖centeredOneResolventTrace d f lambda z x‖} := by
    ext x
    exact (sq_le_sq₀ hε.le (norm_nonneg _))
  rw [hset] at hmarkov
  have hmoment := integral_norm_sq_centeredOneResolventTrace_le
    hN hd f lambda hz
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [mul_comm]
  exact hmarkov.trans hmoment

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
