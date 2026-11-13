module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierStieltjesJointLaw
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WeightedSquaresLaw
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FourierCriterion

/-!
# Probability-to-Fourier bridge for the APSSS ratio estimate

This module assembles the measure-theoretic first half of APSSS Claim 6.2.  In
particular, the heat kernel majorizes the ratio event with the exact
`exp (1/4)` normalization.  The remaining Fourier-pairing step requires the
(two-dimensional) integrability of the explicit transformed regularized kernel.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The APSSS heat kernel majorizes the ratio event, with the exact exponential
constant and without any assumption on the law beyond finiteness. -/
theorem measure_ratioEvent_le_lintegral_fourierRatioKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXpos : ∀ᵐ ω ∂P, 0 < X ω) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    P {ω | |Y ω - a| ≤ ε * Real.sqrt (X ω)} ≤
      ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) *
        ∫⁻ ω, ENNReal.ofReal (fourierRatioKernel ε (X ω) (Y ω - a)) ∂P := by
  let s : Set Ω := {ω | |Y ω - a| ≤ ε * Real.sqrt (X ω)}
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  rw [show P s = ∫⁻ ω in s, (1 : ℝ≥0∞) ∂P by simp]
  rw [← lintegral_indicator hs]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hXpos] with ω hω
  by_cases hωs : ω ∈ s
  · rw [indicator_of_mem hωs]
    have hk := exp_neg_one_div_four_le_fourierRatioKernel hε hω hωs
    have hexp : 1 ≤ Real.exp (1 / 4 : ℝ) *
        fourierRatioKernel ε (X ω) (Y ω - a) := by
      calc
        1 = Real.exp (1 / 4 : ℝ) * Real.exp (-(1 / 4 : ℝ)) := by
          rw [← Real.exp_add]
          norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    simpa [ENNReal.ofReal_mul (Real.exp_pos _).le] using
      ENNReal.ofReal_le_ofReal hexp
  · rw [indicator_of_notMem hωs]
    exact bot_le

/-- Removal of the positive regularizer directly along `δ → 0+`, rather than
only along the canonical sequence.  This is the filter needed by the
Fourier liminf. -/
theorem tendsto_integral_regularizedFourierRatioKernel_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => ∫ ω,
      regularizedFourierRatioKernel ε δ (X ω) (Y ω) ∂P)
      (𝓝[>] 0)
      (𝓝 (∫ ω, fourierRatioKernel ε (X ω) (Y ω) ∂P)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · exact .of_forall fun δ =>
      (measurable_regularizedFourierRatioKernel ε δ).comp
        (hX.prodMk hY) |>.aestronglyMeasurable
  · refine ⟨1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact .of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_regularizedFourierRatioKernel_le_one hε hδ.le
  · exact .of_forall fun ω => by
      by_cases hx : 0 < X ω
      · simp only [regularizedFourierRatioKernel, fourierRatioKernel, hx, ite_true]
        have he : Tendsto
            (fun δ : ℝ => Real.exp (-δ * X ω)) (𝓝[>] 0) (𝓝 1) := by
          have hc : Continuous (fun δ : ℝ => Real.exp (-δ * X ω)) := by
            fun_prop
          have ht : Tendsto (fun δ : ℝ => Real.exp (-δ * X ω))
              (𝓝[>] 0) (𝓝 (Real.exp (-(0 : ℝ) * X ω))) :=
            hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          simpa using ht
        have hp : Tendsto
            (fun δ : ℝ => X ω ^ δ) (𝓝[>] 0) (𝓝 1) := by
          have hc : ContinuousAt (fun δ : ℝ => X ω ^ δ) 0 :=
            Real.continuousAt_const_rpow hx.ne'
          simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
        have hconst : Tendsto
            (fun _δ : ℝ => Real.exp (-(Y ω) ^ 2 /
              (4 * ε ^ 2 * X ω))) (𝓝[>] 0)
            (𝓝 (Real.exp (-(Y ω) ^ 2 / (4 * ε ^ 2 * X ω)))) :=
          tendsto_const_nhds
        simpa [mul_assoc] using hconst.mul (he.mul hp)
      · simp [regularizedFourierRatioKernel, fourierRatioKernel, hx]

/-- Integral form of the heat-kernel event majorization. -/
theorem measure_ratioEvent_le_ofReal_integral_fourierRatioKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXpos : ∀ᵐ ω ∂P, 0 < X ω) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    P {ω | |Y ω - a| ≤ ε * Real.sqrt (X ω)} ≤
      ENNReal.ofReal (Real.exp (1 / 4 : ℝ) *
        ∫ ω, fourierRatioKernel ε (X ω) (Y ω - a) ∂P) := by
  have hmeas : AEStronglyMeasurable
      (fun ω => fourierRatioKernel ε (X ω) (Y ω - a)) P :=
    (measurable_fourierRatioKernel ε).comp
      (hX.prodMk (hY.sub measurable_const)) |>.aestronglyMeasurable
  have hint : Integrable
      (fun ω => fourierRatioKernel ε (X ω) (Y ω - a)) P := by
    apply Integrable.mono' (integrable_const (μ := P) (1 : ℝ)) hmeas
    filter_upwards with ω
    have hnonneg : 0 ≤ fourierRatioKernel ε (X ω) (Y ω - a) := by
      unfold fourierRatioKernel
      split_ifs <;> positivity
    have hle : fourierRatioKernel ε (X ω) (Y ω - a) ≤ 1 := by
      unfold fourierRatioKernel
      split_ifs with hx
      · rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
      · simp
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hnonneg : ∀ᵐ ω ∂P,
      0 ≤ fourierRatioKernel ε (X ω) (Y ω - a) := by
    filter_upwards with ω
    unfold fourierRatioKernel
    split_ifs <;> positivity
  have h := measure_ratioEvent_le_lintegral_fourierRatioKernel
    P X Y hX hY hXpos hε a
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg] at h
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact h

end PSSSNative.BlockBand.PSSS
