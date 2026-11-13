module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioTransform
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Fourier transform of the regularized ratio kernel

The regularized APSSS ratio kernel, viewed as a function on the Euclidean plane, is integrable,
its Mathlib Fourier transform is given by an explicit closed formula after the `2π` frequency
rescaling, and this transform is integrable.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand.PSSS
open Complex MeasureTheory Set
open scoped ENNReal NNReal Topology FourierTransform

abbrev RegularizedKernelPlane := EuclideanSpace ℝ (Fin 2)
abbrev RegularizedKernelProductPlane := WithLp 2 (ℝ × ℝ)

private def regularizedKernelCoordinateLinearEquiv :
    RegularizedKernelPlane ≃ₗ[ℝ] RegularizedKernelProductPlane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).trans
      (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm)

private def regularizedKernelCoordinateEquiv :
    RegularizedKernelPlane ≃ₗᵢ[ℝ] RegularizedKernelProductPlane :=
  LinearIsometryEquiv.mk regularizedKernelCoordinateLinearEquiv (by
    intro x
    have hx : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    have hy : ‖regularizedKernelCoordinateLinearEquiv x‖ ^ 2 =
        ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [regularizedKernelCoordinateLinearEquiv]
    nlinarith [norm_nonneg x, norm_nonneg (regularizedKernelCoordinateLinearEquiv x)])

/-- The regularized APSSS ratio kernel on the Euclidean Fourier plane. -/
def regularizedKernelEuclidean (ε δ : ℝ) : RegularizedKernelPlane → ℂ :=
  fun x => (regularizedFourierRatioKernel ε δ (x 0) (x 1) : ℂ)

/-- The explicit transform, with the `2π` rescaling required by Mathlib's convention. -/
def explicitRegularizedKernelFourier (ε δ : ℝ)
    (w : RegularizedKernelPlane) : ℂ :=
  2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε /
    ((((2 * Real.pi * w 1) ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) +
      ((2 * Real.pi * w 0 : ℝ) : ℂ) * Complex.I) ^
        (((3 / 2 + δ : ℝ)) : ℂ)

/-- Product-space absolute integrability transported to Euclidean volume. -/
theorem integrable_regularizedKernelEuclidean {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (regularizedKernelEuclidean ε δ) := by
  have hp0 := integrable_fourierRatioIntegrand (ξ := 0) (η := 0) hε hδ
  have hp : Integrable (fun p : ℝ × ℝ =>
      (regularizedFourierRatioKernel ε δ p.1 p.2 : ℂ)) (volume.prod volume) := by
    apply hp0.congr
    filter_upwards with p
    simp [fourierRatioIntegrand]
  have hp' : Integrable (fun p : RegularizedKernelProductPlane =>
      (regularizedFourierRatioKernel ε δ (WithLp.ofLp p).1 (WithLp.ofLp p).2 : ℂ)) :=
    ((WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding).2 hp
  exact (regularizedKernelCoordinateEquiv.measurePreserving.integrable_comp_emb
    regularizedKernelCoordinateEquiv.toHomeomorph.measurableEmbedding).2 hp'

/-- The explicit transform `explicitRegularizedKernelFourier` is Mathlib's Fourier transform of
the regularized kernel, after the `2π` frequency rescaling. -/
theorem fourier_regularizedKernelEuclidean {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (w : RegularizedKernelPlane) :
    𝓕 (regularizedKernelEuclidean ε δ) w =
      explicitRegularizedKernelFourier ε δ w := by
  rw [Real.fourier_eq']
  have hcoord :
      (∫ v : RegularizedKernelPlane,
        Complex.exp ((↑(-2 * Real.pi * inner ℝ v w) * I)) •
          regularizedKernelEuclidean ε δ v) =
      ∫ p : RegularizedKernelProductPlane,
        Complex.exp (-(I *
          (((2 * Real.pi * w 0 : ℝ) : ℂ) * (WithLp.ofLp p).1 +
           ((2 * Real.pi * w 1 : ℝ) : ℂ) * (WithLp.ofLp p).2))) *
          (regularizedFourierRatioKernel ε δ
            (WithLp.ofLp p).1 (WithLp.ofLp p).2 : ℂ) := by
    rw [← regularizedKernelCoordinateEquiv.measurePreserving.integral_comp
      regularizedKernelCoordinateEquiv.toHomeomorph.measurableEmbedding]
    apply integral_congr_ae
    filter_upwards with v
    simp only [regularizedKernelEuclidean,
      regularizedKernelCoordinateEquiv, regularizedKernelCoordinateLinearEquiv]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp
    apply Or.inl
    congr 1
    ring
  rw [hcoord]
  rw [← (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding]
  apply (Eq.trans ?_ (fourier_hDelta hε hδ
    (2 * Real.pi * w 0) (2 * Real.pi * w 1)))
  apply integral_congr_ae
  filter_upwards with p
  simp only [regularizedFourierRatioKernel]
  ring

/-- One-dimensional power decay, in the exponent convention used below. -/
private theorem integrable_one_add_sq_rpow {p : ℝ} (hp : 1 / 2 < p) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-p)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (μ := volume)
    (E := ℝ) (r := 2 * p) (by
      rw [show (Module.finrank ℝ ℝ : ℝ) = 1 by norm_num]
      linarith)
  convert h using 1
  · ext x
    rw [Real.norm_eq_abs, sq_abs]
    congr 2
    ring

/-- A positive anisotropic quadratic has an integrable negative power in one dimension. -/
private theorem integrable_quadratic_rpow {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 1 / 2 < p) :
    Integrable (fun x : ℝ => (a * x ^ 2 + b) ^ (-p)) := by
  let c : ℝ := min a b
  have hc : 0 < c := lt_min ha hb
  have hbase := integrable_one_add_sq_rpow hp
  apply (hbase.const_mul (c ^ (-p))).mono'
  · exact (((continuous_const.mul (continuous_id.pow 2)).add_const b).rpow
      continuous_const (fun x => Or.inl (ne_of_gt (by
        simpa using add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg x)) hb)))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hmul : c * (1 + x ^ 2) ≤ a * x ^ 2 + b := by
      have hca : c ≤ a := min_le_left _ _
      have hcb : c ≤ b := min_le_right _ _
      nlinarith [sq_nonneg x]
    rw [← Real.mul_rpow hc.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hmul (by linarith)

/-- The explicit frequency majorant generated by the regularized kernel transform. -/
def regularizedKernelFrequencyMajorant (ε δ δ' : ℝ) (p : ℝ × ℝ) : ℝ :=
  (((p.1 ^ 2 * ε ^ 2 + δ) ^ 2 + p.2 ^ 2) ^
    (-(3 / 2 + δ') / 2))

private theorem regularizedKernelFrequencyMajorant_slice_integral
    {ε δ δ' η : ℝ} (hδ : 0 < δ) :
    (∫ ξ : ℝ, ‖regularizedKernelFrequencyMajorant ε δ δ' (η, ξ)‖) =
      (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (-(3 / 2 + δ') / 2)) *
        (η ^ 2 * ε ^ 2 + δ) ^ (1 - 2 * ((3 / 2 + δ') / 2)) := by
  let A : ℝ := η ^ 2 * ε ^ 2 + δ
  let p : ℝ := (3 / 2 + δ') / 2
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg ε)]
  have hpoint : ∀ ξ : ℝ,
      ((A ^ 2 + ξ ^ 2) ^ (-p)) =
        A ^ (-2 * p) * (1 + (ξ / A) ^ 2) ^ (-p) := by
    intro ξ
    have hfac : A ^ 2 + ξ ^ 2 = A ^ 2 * (1 + (ξ / A) ^ 2) := by
      field_simp
    rw [hfac, Real.mul_rpow (sq_nonneg A) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hA.le]
    congr 1
    ring
  simp only [regularizedKernelFrequencyMajorant]
  rw [show -(3 / 2 + δ') / 2 = -p by dsimp [p]; ring]
  change (∫ ξ : ℝ, ‖((A ^ 2 + ξ ^ 2) ^ (-p))‖) =
    (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (-p)) * A ^ (1 - 2 * p)
  apply Eq.trans (integral_congr_ae (ae_of_all _ fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _), hpoint]))

  rw [integral_const_mul, Measure.integral_comp_div
    (fun x : ℝ => (1 + x ^ 2) ^ (-p)) A]
  rw [abs_of_pos hA, smul_eq_mul]
  rw [← mul_assoc]
  nth_rewrite 2 [← Real.rpow_one A]
  rw [← Real.rpow_add hA]
  rw [show -2 * p + 1 = 1 - 2 * p by ring]
  exact mul_comm _ _

/-- For every positive regularization and every positive excess exponent, the
explicit anisotropic frequency majorant is integrable on product frequency space. -/
theorem integrable_regularizedKernelFrequencyMajorant {ε δ δ' : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ' : 0 < δ') :
    Integrable (regularizedKernelFrequencyMajorant ε δ δ')
      (volume.prod volume) := by
  have hp : 1 / 2 < (3 / 2 + δ') / 2 := by linarith
  have hmeas : AEStronglyMeasurable
      (regularizedKernelFrequencyMajorant ε δ δ') (volume.prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold regularizedKernelFrequencyMajorant
    refine Continuous.rpow (by fun_prop) continuous_const ?_
    intro x
    apply Or.inl
    have hA : 0 < x.1 ^ 2 * ε ^ 2 + δ := by
      nlinarith [mul_nonneg (sq_nonneg x.1) (sq_nonneg ε)]
    nlinarith [sq_nonneg x.2]
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards with η
    change Integrable (fun ξ : ℝ =>
      (((η ^ 2 * ε ^ 2 + δ) ^ 2 + ξ ^ 2) ^ (-(3 / 2 + δ') / 2)))
    have hs := integrable_quadratic_rpow
      (a := 1) (b := (η ^ 2 * ε ^ 2 + δ) ^ 2)
      (p := (3 / 2 + δ') / 2) (by norm_num)
      (sq_pos_of_pos (by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg ε)])) hp
    simpa only [one_mul, add_comm, neg_div] using hs
  · rw [show (fun η : ℝ => ∫ ξ : ℝ,
        ‖regularizedKernelFrequencyMajorant ε δ δ' (η, ξ)‖) =
      (fun η : ℝ =>
        (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (-(3 / 2 + δ') / 2)) *
          (η ^ 2 * ε ^ 2 + δ) ^ (1 - 2 * ((3 / 2 + δ') / 2))) by
        funext η
        simpa [mul_comm] using
          (regularizedKernelFrequencyMajorant_slice_integral
            (ε := ε) (δ := δ) (δ' := δ') (η := η) hδ)]
    apply Integrable.const_mul
    rw [show 1 - 2 * ((3 / 2 + δ') / 2) = -(1 / 2 + δ') by ring]
    simpa only [mul_comm] using
      (integrable_quadratic_rpow (a := ε ^ 2) (b := δ)
        (p := 1 / 2 + δ') (sq_pos_of_pos hε) hδ (by linarith))

/-- The explicit majorant remains integrable after the Euclidean coordinate swap
and the common `2π` Fourier-frequency rescaling. -/
private theorem integrable_scaled_swapped_frequencyMajorant {ε δ δ' : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ' : 0 < δ') :
    Integrable (fun w : RegularizedKernelPlane =>
      regularizedKernelFrequencyMajorant ε δ δ'
        (2 * Real.pi * w 1, 2 * Real.pi * w 0)) := by
  have hp := (integrable_regularizedKernelFrequencyMajorant hε hδ hδ').swap
  have hp' : Integrable (fun p : RegularizedKernelProductPlane =>
      regularizedKernelFrequencyMajorant ε δ δ'
        ((WithLp.ofLp p).2, (WithLp.ofLp p).1)) :=
    ((WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding).2 hp
  have he : Integrable (fun w : RegularizedKernelPlane =>
      regularizedKernelFrequencyMajorant ε δ δ' (w 1, w 0)) :=
    (regularizedKernelCoordinateEquiv.measurePreserving.integrable_comp_emb
      regularizedKernelCoordinateEquiv.toHomeomorph.measurableEmbedding).2 hp'
  convert he.comp_smul (show (2 * Real.pi : ℝ) ≠ 0 by positivity) using 1
  ext w
  simp [smul_eq_mul]

private theorem norm_explicitRegularizedKernelFourier {ε δ : ℝ}
    (hδ : 0 < δ) (w : RegularizedKernelPlane) :
    ‖explicitRegularizedKernelFourier ε δ w‖ =
      ‖(2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε : ℂ)‖ *
        regularizedKernelFrequencyMajorant ε δ δ
          (2 * Real.pi * w 1, 2 * Real.pi * w 0) := by
  let z := fourierRatioLaplaceParameter ε δ
    (2 * Real.pi * w 0) (2 * Real.pi * w 1)
  let r : ℝ := 3 / 2 + δ
  have hz : z ≠ 0 := fourierRatioLaplaceParameter_ne_zero hδ
  have hsq : ‖z‖ ^ 2 =
      ((2 * Real.pi * w 1) ^ 2 * ε ^ 2 + δ) ^ 2 +
        (2 * Real.pi * w 0) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_fourierRatioLaplaceParameter ε δ
      (2 * Real.pi * w 0) (2 * Real.pi * w 1)
  unfold explicitRegularizedKernelFourier regularizedKernelFrequencyMajorant
  change ‖(2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε : ℂ) / z ^ (r : ℂ)‖ = _
  rw [norm_div, Complex.norm_cpow_real]
  rw [← hsq]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : (‖z‖ ^ 2) ^ (-r / 2) = (‖z‖ ^ r)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (norm_nonneg z)]
    norm_num
    rw [show 2 * (-r / 2) = -r by ring]
    rw [Real.rpow_neg (norm_nonneg z) r]
  rw [hp, div_eq_mul_inv]

/-- The Mathlib Fourier transform of the regularized kernel is integrable. -/
theorem integrable_fourier_regularizedKernelEuclidean {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (𝓕 (regularizedKernelEuclidean ε δ)) := by
  have hm := (integrable_scaled_swapped_frequencyMajorant hε hδ hδ).const_mul
    ‖(2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε : ℂ)‖
  have hn : Integrable (fun w : RegularizedKernelPlane =>
      ‖𝓕 (regularizedKernelEuclidean ε δ) w‖) := by
    apply hm.congr
    filter_upwards with w
    rw [fourier_regularizedKernelEuclidean hε hδ]
    exact (norm_explicitRegularizedKernelFourier (ε := ε) hδ w).symm
  have hc : Continuous (𝓕 (regularizedKernelEuclidean ε δ)) := by
    exact VectorFourier.fourierIntegral_continuous
      (L := (innerSL ℝ : RegularizedKernelPlane →L[ℝ]
        RegularizedKernelPlane →L[ℝ] ℝ).toLinearMap₁₂)
      Real.continuous_fourierChar continuous_inner
      (integrable_regularizedKernelEuclidean hε hδ)
  exact (integrable_norm_iff hc.aestronglyMeasurable).1 hn

end PSSSNative.BlockBand.PSSS
