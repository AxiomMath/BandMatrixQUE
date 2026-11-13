module

public import BlockBand.SourceProcess.ClosingLeak.PathLeak

/-!
# Jensen for one leaked mass: `E (leakTerm_{il})^{1/2} ≤ ((2/M) E Re Tr(A_- Q(q_i)))^{1/2}`

`lintegral_sqrt_le` is Jensen (Cauchy–Schwarz against `1`) for `√` under a probability measure,
in `ℝ≥0∞` so that no integrability is needed. `lintegral_sqrt_leakTerm_le` combines it with
`eventually_lintegral_leakTerm`: if `E Re Tr(A_- Q(q_i)) ≤ M δ²/2` (and the integrand is
integrable), then `∫⁻ (leakTerm_{il})^{1/2} ≤ δ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Sampling BlockBand.SourceProcess.ClosingAux
open scoped ComplexOrder

/-- **Jensen for `√`**: `∫⁻ √f ≤ (∫⁻ f)^{1/2}` under a probability measure, `f ≥ 0`. -/
theorem lintegral_sqrt_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (Real.sqrt (f x)) ∂μ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ^ (1 / 2 : ℝ) := by
  have hF : Measurable fun x => ENNReal.ofReal (Real.sqrt (f x)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hf)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF.aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) zero_le_two, Real.rpow_two,
    Real.sq_sqrt (hf0 x)]

variable {W : ℕ}

theorem leakTerm_nonneg (b E s T h : ℝ) {p : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (M W : ℕ) (il : Fin p × Fin M) (y : SampledPath W p M × ℝ) :
    0 ≤ leakTerm b E s T h q M W il y :=
  re_trace_mul_nonneg (posSemidef_self_mul_conjTranspose _)
    (rankOne_psd _ (div_nonneg (gridMass_nonneg W _ (hq il.1)) (by positivity)) _)

theorem isProbabilityMeasure_sampledPathLaw (b : ℝ) (W n : ℕ) {p : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) (M : ℕ) : IsProbabilityMeasure (sampledPathLaw b W n q M) := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W n (hq x.1)
  unfold sampledPathLaw; infer_instance

/-- **One leaked mass after Jensen.** If the expected path leak of test `i` is at most `Mδ²/2`,
then `∫⁻ (leakTerm_{il})^{1/2} ≤ δ`. -/
theorem lintegral_sqrt_leakTerm_le {b E s T h : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {M : ℕ} (hM : 0 < M) (il : Fin p × Fin M) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL : ∫⁻ y, ENNReal.ofReal (leakTerm b E s T h q M W il y)
          ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) =
        ∫⁻ ω, ENNReal.ofReal (2 / M * (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
          intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re) ∂growthPathLaw W b)
    (hI : Integrable (fun ω => (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re) (growthPathLaw W b))
    (hε : ∫ ω, (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re ∂growthPathLaw W b ≤ M * δ ^ 2 / 2) :
    ∫⁻ y, ENNReal.ofReal (Real.sqrt (leakTerm b E s T h q M W il y))
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) ≤ ENNReal.ofReal δ := by
  have := isProbabilityMeasure_sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ hq M
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  refine (lintegral_sqrt_le (measurable_leakTerm b E s T h q M W il)
    (leakTerm_nonneg b E s T h hq M W il)).trans ?_
  rw [hL, ← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) (ae_of_all _ fun ω =>
    mul_nonneg (by positivity) (re_trace_mul_nonneg (farEmbed_omittedProj_psd b E h _ ω)
      (intervalSource_psd b E _ (hq il.1) ω))), integral_const_mul]
  have h1 : 2 / M * ∫ ω, (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re ∂growthPathLaw W b ≤ δ ^ 2 := by
    calc _ ≤ 2 / M * (M * δ ^ 2 / 2) := mul_le_mul_of_nonneg_left hε (by positivity)
      _ = δ ^ 2 := by field_simp
  calc ENNReal.ofReal (2 / M * ∫ ω, (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re ∂growthPathLaw W b) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (δ ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) (by norm_num)
    _ = ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg δ) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hδ]

end BlockBand.SourceProcess.ClosingLeak
