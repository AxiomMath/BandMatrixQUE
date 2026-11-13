module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FourierProbabilityBridge
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RegularizedKernelProbabilityAdapter

/-!
# The APSSS ratio tail Fourier bound

This module completes the Fourier reduction in Claim 6.2 of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin).  The
change from Mathlib's Euclidean Fourier variable to the paper's two real
frequencies has Jacobian `(2π)⁻²`; translation by `a` contributes only the
unit-modulus phase `exp (-iηa)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal Topology FourierTransform

private def ratioFrequencyCoordinateLinearEquiv :
    RegularizedKernelPlane ≃ₗ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).trans
      (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm)

private def ratioFrequencyCoordinateEquiv :
    RegularizedKernelPlane ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) :=
  LinearIsometryEquiv.mk ratioFrequencyCoordinateLinearEquiv (by
    intro x
    have hx : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    have hy : ‖ratioFrequencyCoordinateLinearEquiv x‖ ^ 2 =
        ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [ratioFrequencyCoordinateLinearEquiv]
    nlinarith [norm_nonneg x, norm_nonneg (ratioFrequencyCoordinateLinearEquiv x)])

private def jointRandomVector {Ω : Type*} (X Y : Ω → ℝ) (a : ℝ) :
    Ω → RegularizedKernelPlane := fun ω =>
  WithLp.toLp 2 ![X ω, Y ω - a]

private def jointCharacteristic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (ξ η : ℝ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ((ξ : ℂ) * X ω + (η : ℂ) * Y ω)) ∂P

private def ratioFourierIntegrand {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (ε δ ξ η : ℝ) : ℂ :=
  jointCharacteristic P X Y ξ η /
    ((((η ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) ^
      (((3 / 2 + δ : ℝ)) : ℂ))

private theorem shifted_jointCharacteristic_eq_phase
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → ℝ) (a ξ η : ℝ) :
    (∫ ω, Complex.exp (Complex.I *
      ((ξ : ℂ) * X ω + (η : ℂ) * (Y ω - a))) ∂P) =
      Complex.exp (-(Complex.I * (η : ℂ) * (a : ℂ))) *
        jointCharacteristic P X Y ξ η := by
  unfold jointCharacteristic
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem regularized_expectation_eq_euclidean_fourier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∫ ω, (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ) ∂P) =
      ∫ q : RegularizedKernelPlane,
        (∫ ω, Complex.exp
          (((2 * Real.pi * inner ℝ q (jointRandomVector X Y a ω) : ℝ) : ℂ) *
            Complex.I) ∂P) * explicitRegularizedKernelFourier ε δ q := by
  let Z : Ω → RegularizedKernelPlane := jointRandomVector X Y a
  have hZ : Measurable Z := by
    dsimp [Z]
    unfold jointRandomVector
    fun_prop
  have hcont : ∀ᵐ ω ∂P, ContinuousAt (regularizedKernelEuclidean ε δ) (Z ω) :=
    ae_of_all _ fun _ => (continuous_regularizedKernelEuclidean hδ).continuousAt
  have h := integral_comp_eq_integral_fourier_mul_char P Z hZ hcont
    (integrable_regularizedKernelEuclidean hε hδ)
    (integrable_fourier_regularizedKernelEuclidean hε hδ)
  rw [show (fun ω => regularizedKernelEuclidean ε δ (Z ω)) =
      (fun ω => (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ)) by
    funext ω
    simp [Z, jointRandomVector, regularizedKernelEuclidean]] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with q
  rw [fourier_regularizedKernelEuclidean hε hδ]

private def paperEuclideanIntegrand {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (a ε δ : ℝ)
    (q : RegularizedKernelPlane) : ℂ :=
  Complex.exp (-(Complex.I * (q 1 : ℂ) * (a : ℂ))) *
    (2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε : ℂ) *
      ratioFourierIntegrand P X Y ε δ (q 0) (q 1)

private def paperProductIntegrand {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (a ε δ : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (p.2 : ℂ) * (a : ℂ))) *
    (2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε : ℂ) *
      ratioFourierIntegrand P X Y ε δ p.1 p.2

private theorem euclideanFourierIntegrand_eq_scaled_paper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a : ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (q : RegularizedKernelPlane) :
    (∫ ω, Complex.exp
      (((2 * Real.pi * inner ℝ q (jointRandomVector X Y a ω) : ℝ) : ℂ) *
        Complex.I) ∂P) * explicitRegularizedKernelFourier ε δ q =
      paperEuclideanIntegrand P X Y a ε δ ((2 * Real.pi) • q) := by
  have hinner : ∀ ω,
      2 * Real.pi * inner ℝ q (jointRandomVector X Y a ω) =
        (2 * Real.pi * q 0) * X ω + (2 * Real.pi * q 1) * (Y ω - a) := by
    intro ω
    simp [jointRandomVector, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  simp_rw [hinner]
  have hexp : ∀ ω,
      Complex.exp (((2 * Real.pi * q 0 * X ω +
        2 * Real.pi * q 1 * (Y ω - a) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I *
        (((2 * Real.pi * q 0 : ℝ) : ℂ) * X ω +
          ((2 * Real.pi * q 1 : ℝ) : ℂ) * (Y ω - a))) := by
    intro ω
    congr 1
    push_cast
    ring
  simp_rw [hexp]
  rw [shifted_jointCharacteristic_eq_phase P X Y a
    (2 * Real.pi * q 0) (2 * Real.pi * q 1)]
  unfold paperEuclideanIntegrand ratioFourierIntegrand
    explicitRegularizedKernelFourier
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hden : ((((2 * Real.pi * q 1) ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) +
      ((2 * Real.pi * q 0 : ℝ) : ℂ) * Complex.I) ^
        (((3 / 2 + δ : ℝ)) : ℂ) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (fourierRatioLaplaceParameter_ne_zero hδ))
  field_simp

private theorem integrable_euclideanFourierIntegrand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (fun q : RegularizedKernelPlane =>
      (∫ ω, Complex.exp
        (((2 * Real.pi * inner ℝ q (jointRandomVector X Y a ω) : ℝ) : ℂ) *
          Complex.I) ∂P) * explicitRegularizedKernelFourier ε δ q) := by
  let Z : Ω → RegularizedKernelPlane := jointRandomVector X Y a
  have hZ : Measurable Z := by
    dsimp [Z]
    unfold jointRandomVector
    fun_prop
  have hk := integrable_fourierStieltjesKernel_comp P Z hZ
    (integrable_regularizedKernelEuclidean hε hδ)
    (integrable_fourier_regularizedKernelEuclidean hε hδ)
  have hi := hk.integral_prod_right
  apply hi.congr
  filter_upwards with q
  unfold fourierStieltjesKernel
  change (∫ x : Ω, Complex.exp
      (((2 * Real.pi * inner ℝ q (Z x) : ℝ) : ℂ) * Complex.I) *
        𝓕 (regularizedKernelEuclidean ε δ) q ∂P) = _
  rw [integral_mul_const, fourier_regularizedKernelEuclidean hε hδ]

private theorem integrable_paperEuclideanIntegrand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (paperEuclideanIntegrand P X Y a ε δ) := by
  have hi := integrable_euclideanFourierIntegrand P X Y hX hY a hε hδ
  have hiscaled : Integrable (fun q : RegularizedKernelPlane =>
      paperEuclideanIntegrand P X Y a ε δ ((2 * Real.pi) • q)) := by
    apply hi.congr
    filter_upwards with q
    exact euclideanFourierIntegrand_eq_scaled_paper P X Y a hδ q
  exact (integrable_comp_smul_iff volume
    (paperEuclideanIntegrand P X Y a ε δ)
    (show (2 * Real.pi : ℝ) ≠ 0 by positivity)).1 hiscaled

private theorem integrable_paperProductIntegrand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (paperProductIntegrand P X Y a ε δ) (volume.prod volume) := by
  have he := integrable_paperEuclideanIntegrand P X Y hX hY a hε hδ
  have hlp : Integrable (fun p : WithLp 2 (ℝ × ℝ) =>
      paperProductIntegrand P X Y a ε δ (WithLp.ofLp p)) := by
    apply (ratioFrequencyCoordinateEquiv.measurePreserving.integrable_comp_emb
      ratioFrequencyCoordinateEquiv.toHomeomorph.measurableEmbedding).1
    convert he using 1
    ext q
    simp [paperEuclideanIntegrand, paperProductIntegrand,
      ratioFrequencyCoordinateEquiv, ratioFrequencyCoordinateLinearEquiv]
  exact ((WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding).1 hlp

private theorem regularized_expectation_eq_paper_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∫ ω, (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ) ∂P) =
      ((2 * Real.pi) ^ 2)⁻¹ •
        ∫ η : ℝ, ∫ ξ : ℝ,
          paperProductIntegrand P X Y a ε δ (ξ, η) := by
  rw [regularized_expectation_eq_euclidean_fourier P X Y hX hY a hε hδ]
  calc
    (∫ q : RegularizedKernelPlane,
        (∫ ω, Complex.exp
          (((2 * Real.pi * inner ℝ q (jointRandomVector X Y a ω) : ℝ) : ℂ) *
            Complex.I) ∂P) * explicitRegularizedKernelFourier ε δ q) =
      ∫ q : RegularizedKernelPlane,
        paperEuclideanIntegrand P X Y a ε δ ((2 * Real.pi) • q) := by
          apply integral_congr_ae
          filter_upwards with q
          exact euclideanFourierIntegrand_eq_scaled_paper P X Y a hδ q
    _ = ((2 * Real.pi) ^ 2)⁻¹ •
        ∫ q : RegularizedKernelPlane,
          paperEuclideanIntegrand P X Y a ε δ q := by
      simpa [show Module.finrank ℝ RegularizedKernelPlane = 2 by norm_num,
        smul_eq_mul] using
        (Measure.integral_comp_smul_of_nonneg volume
          (paperEuclideanIntegrand P X Y a ε δ) (2 * Real.pi)
          (hR := by positivity))
    _ = ((2 * Real.pi) ^ 2)⁻¹ •
        (∫ p : ℝ × ℝ, paperProductIntegrand P X Y a ε δ p
          ∂volume.prod volume) := by
      congr 1
      calc
        (∫ q : RegularizedKernelPlane,
            paperEuclideanIntegrand P X Y a ε δ q) =
          ∫ q : RegularizedKernelPlane,
            paperProductIntegrand P X Y a ε δ
              (WithLp.ofLp (ratioFrequencyCoordinateEquiv q)) := by
            apply integral_congr_ae
            filter_upwards with q
            simp [paperEuclideanIntegrand, paperProductIntegrand,
              ratioFrequencyCoordinateEquiv, ratioFrequencyCoordinateLinearEquiv]
        _ = ∫ p : WithLp 2 (ℝ × ℝ),
            paperProductIntegrand P X Y a ε δ (WithLp.ofLp p) :=
          ratioFrequencyCoordinateEquiv.measurePreserving.integral_comp
            ratioFrequencyCoordinateEquiv.toHomeomorph.measurableEmbedding
            (fun p : WithLp 2 (ℝ × ℝ) =>
              paperProductIntegrand P X Y a ε δ (WithLp.ofLp p))
        _ = ∫ p : ℝ × ℝ, paperProductIntegrand P X Y a ε δ p
            ∂volume.prod volume := by
          rw [← (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
            (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding]
          rfl
    _ = ((2 * Real.pi) ^ 2)⁻¹ •
        ∫ η : ℝ, ∫ ξ : ℝ,
          paperProductIntegrand P X Y a ε δ (ξ, η) := by
      rw [integral_prod_symm _
        (integrable_paperProductIntegrand P X Y hX hY a hε hδ)]

private def regularizedPaperCoefficient (ε δ : ℝ) : ℝ :=
  2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε

private def ratioFourierLintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (ε δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ η : ℝ, ‖∫ ξ : ℝ,
    ratioFourierIntegrand P X Y ε δ ξ η‖ₑ

private theorem integral_paperProductIntegrand_slice
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (a ε δ η : ℝ) :
    (∫ ξ : ℝ, paperProductIntegrand P X Y a ε δ (ξ, η)) =
      Complex.exp (-(Complex.I * (η : ℂ) * (a : ℂ))) *
        (regularizedPaperCoefficient ε δ : ℂ) *
          ∫ ξ : ℝ, ratioFourierIntegrand P X Y ε δ ξ η := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold paperProductIntegrand regularizedPaperCoefficient
  push_cast
  ring

private theorem regularized_integral_ofReal_le_fourier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ENNReal.ofReal (∫ ω,
      regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) ∂P) ≤
      ENNReal.ofReal
          (regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2) *
        ratioFourierLintegral P X Y ε δ := by
  have hcoeff : 0 ≤ regularizedPaperCoefficient ε δ := by
    unfold regularizedPaperCoefficient
    have hgamma : 0 < Real.Gamma (3 / 2 + δ) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have hjac : 0 ≤ ((2 * Real.pi) ^ 2)⁻¹ := by positivity
  have hint : Integrable (fun ω =>
      (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ)) P := by
    apply Integrable.mono' (integrable_const (μ := P) (1 : ℝ))
    · apply Measurable.aestronglyMeasurable
      exact Complex.continuous_ofReal.measurable.comp
        ((measurable_regularizedFourierRatioKernel ε δ).comp
          (hX.prodMk (hY.sub measurable_const)))
    · filter_upwards with ω
      rw [Complex.norm_real]
      simpa using abs_regularizedFourierRatioKernel_le_one hε hδ.le
  let Ec : ℂ := ∫ ω,
    (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ) ∂P
  have hre : Ec.re = ∫ ω,
      regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) ∂P := by
    dsimp [Ec]
    change RCLike.re (∫ ω,
      (regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) : ℂ) ∂P) = _
    rw [← integral_re hint]
    simp
  calc
    ENNReal.ofReal (∫ ω,
        regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) ∂P) =
      ENNReal.ofReal Ec.re := by rw [hre]
    _ ≤ ENNReal.ofReal ‖Ec‖ := ENNReal.ofReal_le_ofReal (Complex.re_le_norm Ec)
    _ = ‖Ec‖ₑ := ofReal_norm Ec
    _ = ‖((2 * Real.pi) ^ 2)⁻¹ •
        (∫ η : ℝ, ∫ ξ : ℝ,
          paperProductIntegrand P X Y a ε δ (ξ, η))‖ₑ := by
      congr 1
      dsimp [Ec]
      exact regularized_expectation_eq_paper_integral P X Y hX hY a hε hδ
    _ =
      ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
        ‖∫ η : ℝ, ∫ ξ : ℝ,
          paperProductIntegrand P X Y a ε δ (ξ, η)‖ₑ := by
      rw [enorm_smul]
      congr 1
      rw [← ofReal_norm]
      simp [Real.norm_eq_abs]
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
        ∫⁻ η : ℝ, ‖∫ ξ : ℝ,
          paperProductIntegrand P X Y a ε δ (ξ, η)‖ₑ := by
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    _ = ENNReal.ofReal
          (regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2) *
        ratioFourierLintegral P X Y ε δ := by
      unfold ratioFourierLintegral
      have hslice : ∀ η : ℝ,
          ‖∫ ξ : ℝ, paperProductIntegrand P X Y a ε δ (ξ, η)‖ₑ =
            ENNReal.ofReal (regularizedPaperCoefficient ε δ) *
              ‖∫ ξ : ℝ, ratioFourierIntegrand P X Y ε δ ξ η‖ₑ := by
        intro η
        rw [integral_paperProductIntegrand_slice]
        rw [enorm_mul, enorm_mul]
        have hphase : ‖Complex.exp (-(Complex.I * (η : ℂ) * (a : ℂ)))‖ₑ = 1 := by
          rw [← ofReal_norm]
          simp [Complex.norm_exp, Complex.mul_re]
        rw [hphase, one_mul]
        congr 1
        rw [← ofReal_norm]
        simp [Complex.norm_real, abs_of_nonneg hcoeff]
      simp_rw [hslice, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((2 * Real.pi) ^ 2)⁻¹)]
      congr 1
      field_simp

private theorem regularizedPaperCoefficient_zero (ε : ℝ) :
    regularizedPaperCoefficient ε 0 / (2 * Real.pi) ^ 2 =
      ε / (4 * Real.pi) := by
  unfold regularizedPaperCoefficient
  have hgamma : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_half 1 using 1 <;> norm_num
  simp only [add_zero]
  rw [hgamma]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp [Real.pi_ne_zero]
  rw [hpi]
  ring

private theorem tendsto_regularizedPaperCoefficient_zero (ε : ℝ) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal
      (regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (ε / (4 * Real.pi)))) := by
  have hG0 : ContinuousAt Real.Gamma (3 / 2 : ℝ) :=
    (Real.differentiableAt_Gamma (s := (3 / 2 : ℝ)) (by
      intro m
      have hm : (-(m : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      norm_num
      linarith)).continuousAt
  have hG : ContinuousAt
      (fun δ : ℝ => Real.Gamma ((3 / 2 : ℝ) + δ)) 0 :=
    (hG0.comp_of_eq (continuousAt_const.add continuousAt_id) (by norm_num))
  have hc : ContinuousAt (fun δ : ℝ =>
      regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2) 0 := by
    unfold regularizedPaperCoefficient
    exact ((continuousAt_const.mul hG).mul continuousAt_const).div_const _
  have ht : Tendsto (fun δ : ℝ =>
      regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2)
      (𝓝[>] 0) (𝓝 (regularizedPaperCoefficient ε 0 / (2 * Real.pi) ^ 2)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  change Tendsto (ENNReal.ofReal ∘ fun δ : ℝ =>
      regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2)
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal (ε / (4 * Real.pi))))
  simpa only [regularizedPaperCoefficient_zero] using hof

/-- APSSS Claim 6.2 for a general translated ratio event.  The positive
regularizer is removed as a one-sided liminf, and the displayed constant is
exactly `exp (1/4) * ε / (4π)` after the two-dimensional Fourier Jacobian. -/
theorem ratio_tail_le_fourier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXpos : ∀ᵐ ω ∂P, 0 < X ω) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    P {ω | |Y ω - a| ≤ ε * Real.sqrt (X ω)} ≤
      ENNReal.ofReal (Real.exp (1 / 4) * ε / (4 * Real.pi)) *
        Filter.liminf (fun δ : ℝ => ∫⁻ η : ℝ,
          ‖∫ ξ : ℝ,
            (∫ ω, Complex.exp (Complex.I *
              ((ξ : ℂ) * X ω + (η : ℂ) * Y ω)) ∂P) /
              (((η ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) +
                (ξ : ℂ) * Complex.I) ^
                (((3 / 2 + δ : ℝ)) : ℂ)‖ₑ)
          (nhdsWithin 0 (Set.Ioi 0)) := by
  let F : Filter ℝ := 𝓝[>] 0
  let A : ℝ → ℝ≥0∞ := fun δ => ENNReal.ofReal (∫ ω,
    regularizedFourierRatioKernel ε δ (X ω) (Y ω - a) ∂P)
  let C : ℝ → ℝ≥0∞ := fun δ => ENNReal.ofReal
    (regularizedPaperCoefficient ε δ / (2 * Real.pi) ^ 2)
  let L : ℝ → ℝ≥0∞ := fun δ => ratioFourierLintegral P X Y ε δ
  have hreg := tendsto_integral_regularizedFourierRatioKernel_zero
    P X (fun ω => Y ω - a) hX (hY.sub measurable_const) hε
  have hA : Tendsto A F (𝓝 (ENNReal.ofReal
      (∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P))) := by
    dsimp [A, F]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreg
  have hC : Tendsto C F
      (𝓝 (ENNReal.ofReal (ε / (4 * Real.pi)))) := by
    simpa [C, F] using tendsto_regularizedPaperCoefficient_zero ε
  have hle : ∀ᶠ δ in F, A δ ≤ C δ * L δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact regularized_integral_ofReal_le_fourier P X Y hX hY a hε hδ
  have hlim : ENNReal.ofReal
      (∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P) ≤
      Filter.liminf (fun δ => C δ * L δ) F := by
    rw [← hA.liminf_eq]
    exact Filter.liminf_le_liminf hle
  have hcpos : ENNReal.ofReal (ε / (4 * Real.pi)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (by positivity)
  have hctop : ENNReal.ofReal (ε / (4 * Real.pi)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hprod : Filter.liminf (fun δ => C δ * L δ) F ≤
      ENNReal.ofReal (ε / (4 * Real.pi)) * Filter.liminf L F := by
    change Filter.liminf (C * L) F ≤
      ENNReal.ofReal (ε / (4 * Real.pi)) * Filter.liminf L F
    have hm := ENNReal.liminf_mul_le (f := F) (u := C) (v := L)
      (Or.inl (by rw [hC.limsup_eq]; exact hcpos))
      (Or.inl (by rw [hC.limsup_eq]; exact hctop))
    rw [hC.limsup_eq] at hm
    exact hm
  have hfourier : ENNReal.ofReal
      (∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P) ≤
      ENNReal.ofReal (ε / (4 * Real.pi)) * Filter.liminf L F :=
    hlim.trans hprod
  have hp := measure_ratioEvent_le_ofReal_integral_fourierRatioKernel
    P X Y hX hY hXpos hε a
  calc
    P {ω | |Y ω - a| ≤ ε * Real.sqrt (X ω)} ≤
        ENNReal.ofReal (Real.exp (1 / 4) *
          ∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P) := hp
    _ = ENNReal.ofReal (Real.exp (1 / 4)) *
        ENNReal.ofReal
          (∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp (1 / 4)) *
        (ENNReal.ofReal (ε / (4 * Real.pi)) * Filter.liminf L F) := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (1 / 4) * ε / (4 * Real.pi)) *
        Filter.liminf (fun δ : ℝ => ∫⁻ η : ℝ,
          ‖∫ ξ : ℝ,
            (∫ ω, Complex.exp (Complex.I *
              ((ξ : ℂ) * X ω + (η : ℂ) * Y ω)) ∂P) /
              (((η ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) +
                (ξ : ℂ) * Complex.I) ^
                (((3 / 2 + δ : ℝ)) : ℂ)‖ₑ)
          (nhdsWithin 0 (Set.Ioi 0)) := by
      dsimp [L, F, ratioFourierLintegral, ratioFourierIntegrand,
        jointCharacteristic]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      ring

end PSSSNative.BlockBand.PSSS
