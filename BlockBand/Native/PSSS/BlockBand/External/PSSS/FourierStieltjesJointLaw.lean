module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioRegularizerRemoval

/-!
# Fourier–Stieltjes inversion along a measurable joint law

This module applies the proved Fourier inversion kernel directly to a measurable
random vector.  The pointwise inversion hypothesis is required only almost
everywhere under the original law, which is the form needed when the APSSS heat
kernel is extended by zero across `x = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex FourierTransform MeasureTheory
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Absolute product integrability of the Fourier–Stieltjes kernel after
composition with a measurable random vector. -/
theorem integrable_fourierStieltjesKernel_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → V) (hZ : Measurable Z) {f : V → ℂ}
    (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    Integrable (fun p : Ω × V => fourierStieltjesKernel f (Z p.1, p.2))
      (μ.prod volume) := by
  have hFcont : Continuous (𝓕 f) := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hf
  have hmeas : Measurable
      (fun p : Ω × V => fourierStieltjesKernel f (Z p.1, p.2)) := by
    unfold fourierStieltjesKernel
    apply Measurable.mul
    · fun_prop
    · exact hFcont.measurable.comp measurable_snd
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun ω => by
      apply Integrable.mono' hF.norm
      · exact (hmeas.comp measurable_prodMk_left).aestronglyMeasurable
      · filter_upwards with ξ
        simp [fourierStieltjesKernel, Complex.norm_exp]
  · have hc : Integrable (fun _ω : Ω => ∫ ξ : V, ‖𝓕 f ξ‖) μ :=
      integrable_const _
    apply hc.congr
    filter_upwards with ω
    apply integral_congr_ae
    filter_upwards with ξ
    simp [fourierStieltjesKernel, Complex.norm_exp]

/-- Fourier–Stieltjes inversion paired directly with a measurable random vector.
Only almost-everywhere continuity at the values of that vector is used. -/
theorem integral_comp_eq_integral_fourier_mul_char
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → V) (hZ : Measurable Z) {f : V → ℂ}
    (hfcont : ∀ᵐ ω ∂μ, ContinuousAt f (Z ω))
    (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    ∫ ω : Ω, f (Z ω) ∂μ =
      ∫ ξ : V, (∫ ω : Ω,
        Complex.exp (((2 * Real.pi * inner ℝ ξ (Z ω) : ℝ) : ℂ) * Complex.I) ∂μ) *
          𝓕 f ξ := by
  calc
    ∫ ω : Ω, f (Z ω) ∂μ =
        ∫ ω : Ω, (∫ ξ : V, fourierStieltjesKernel f (Z ω, ξ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfcont] with ω hω
      have h := hf.fourierInv_fourier_eq hF hω
      rw [Real.fourierInv_eq'] at h
      simpa [fourierStieltjesKernel, smul_eq_mul] using h.symm
    _ = ∫ p : Ω × V, fourierStieltjesKernel f (Z p.1, p.2) ∂μ.prod volume := by
      exact (integral_prod _
        (integrable_fourierStieltjesKernel_comp μ Z hZ hf hF)).symm
    _ = ∫ ξ : V, ∫ ω : Ω, fourierStieltjesKernel f (Z ω, ξ) ∂μ := by
      exact integral_prod_symm _
        (integrable_fourierStieltjesKernel_comp μ Z hZ hf hF)
    _ = ∫ ξ : V, (∫ ω : Ω,
        Complex.exp (((2 * Real.pi * inner ℝ ξ (Z ω) : ℝ) : ℂ) * Complex.I) ∂μ) *
          𝓕 f ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← integral_mul_const]
      rfl

end PSSSNative.BlockBand.PSSS
