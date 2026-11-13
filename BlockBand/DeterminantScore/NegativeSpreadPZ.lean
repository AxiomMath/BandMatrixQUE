module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Paley–Zygmund and Chebyshev bound for the negative spread

Paley–Zygmund applied to `√U` gives `P(U ≥ A/8) ≥ 1/8`, and Chebyshev for `log U` then implies
`A ≤ 8e⁴e^{E log U}`. Abstract form, on any probability space: for a measurable `V > 0` a.s. with
`E V < ∞`, `Var √V ≤ E V / 2` and `Var log V ≤ 2`, one has `E V ≤ 8e⁴ exp(E log V)`
(`integral_le_of_sqrt_log_spread`). The Paley–Zygmund bound uses the pointwise inequality
`√V ≤ a/2 + V/(2c) + (c/2)1{√V > a/2}`, `a = E√V`, `c = √(8 E V)`; Chebyshev is Mathlib's
`meas_ge_le_evariance_div_sq`. All constants are absolute.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Paley–Zygmund + Chebyshev**: if `V > 0` a.s. is integrable, `Var √V ≤ E V/2` and
`Var log V ≤ 2`, then `E V ≤ 8e⁴ exp(E log V)`. -/
theorem integral_le_of_sqrt_log_spread {V : Ω → ℝ} (hV : Measurable V)
    (hpos : ∀ᵐ ω ∂μ, 0 < V ω) (hint : Integrable V μ)
    (hsq : evariance (fun ω => Real.sqrt (V ω)) μ ≤ ENNReal.ofReal ((∫ ω, V ω ∂μ) / 2))
    (hlog : evariance (fun ω => Real.log (V ω)) μ ≤ 2) :
    ∫ ω, V ω ∂μ ≤ 8 * Real.exp 4 * Real.exp (∫ ω, Real.log (V ω) ∂μ) := by
  set A := ∫ ω, V ω ∂μ with hAdef
  set Y : Ω → ℝ := fun ω => Real.sqrt (V ω) with hYdef
  have hA0 : 0 ≤ A := integral_nonneg_of_ae (hpos.mono fun ω h => h.le)
  have hYmeas : Measurable Y := Real.continuous_sqrt.measurable.comp hV
  have hYm : AEStronglyMeasurable Y μ := hYmeas.aestronglyMeasurable
  have hYsq : ∀ᵐ ω ∂μ, Y ω ^ 2 = V ω := hpos.mono fun ω h => Real.sq_sqrt h.le
  have hY2 : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hYm).2 (hint.congr (hYsq.mono fun ω h => h.symm))
  have hYint : Integrable Y μ := hY2.integrable one_le_two
  set a := ∫ ω, Y ω ∂μ with hadef
  have ha0 : 0 ≤ a := integral_nonneg fun ω => Real.sqrt_nonneg _
  have hvar : variance Y μ = A - a ^ 2 := by
    rw [variance_eq_sub hY2]
    congr 1
    exact integral_congr_ae (hYsq.mono fun ω h => by simpa using h)
  have hvarle : A - a ^ 2 ≤ A / 2 := by
    rw [← hvar]
    have h1 := hY2.ofReal_variance_eq
    rw [← h1] at hsq
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsq
  -- the logarithm
  set L : Ω → ℝ := fun ω => Real.log (V ω) with hLdef
  have hLmeas : Measurable L := Real.measurable_log.comp hV
  have hLm : AEStronglyMeasurable L μ := hLmeas.aestronglyMeasurable
  set M := ∫ ω, L ω ∂μ with hMdef
  by_contra hcon
  push Not at hcon
  have hApos : 0 < A := lt_of_le_of_lt (by positivity) hcon
  set s : ℝ := Real.log (A / 8) - M with hsdef
  have hs4 : 4 < s := by
    have h1 : Real.exp (4 + M) < A / 8 := by
      rw [Real.exp_add]; linarith
    have h2 := (Real.lt_log_iff_exp_lt (by positivity)).2 h1
    rw [hsdef]; linarith
  have hspos : 0 < s := by linarith
  set B : Set Ω := {ω | a / 2 < Y ω} with hBdef
  have hBm : MeasurableSet B := measurableSet_lt measurable_const hYmeas
  -- `B ⊆ {s ≤ |L - M|}` almost surely
  have hBsub : B ≤ᵐ[μ] {ω | ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ |L ω - μ[L]|} := by
    filter_upwards [hpos, hYsq] with ω hω hωY hωB
    simp only [Set.mem_ofPred_eq, hBdef] at hωB ⊢
    rw [Real.coe_toNNReal _ hspos.le]
    have hY : a / 2 < Y ω := hωB
    have hV8 : A / 8 < V ω := by
      have : (a / 2) ^ 2 < Y ω ^ 2 := by
        apply pow_lt_pow_left₀ hY (by positivity) two_ne_zero
      nlinarith
    have hlogV : Real.log (A / 8) < L ω := Real.log_lt_log (by positivity) hV8
    have : s ≤ L ω - M := by rw [hsdef]; linarith
    exact this.trans (le_abs_self _)
  have hcheb := meas_ge_le_evariance_div_sq hLm
    (c := Real.toNNReal s) (by simp [hspos])
  have hPB : μ B < ENNReal.ofReal (1 / 8) := by
    calc μ B ≤ μ {ω | ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ |L ω - μ[L]|} := measure_mono_ae hBsub
      _ ≤ evariance L μ / ((Real.toNNReal s : ℝ≥0) : ℝ≥0∞) ^ 2 := hcheb
      _ ≤ 2 / ((Real.toNNReal s : ℝ≥0) : ℝ≥0∞) ^ 2 := by gcongr
      _ = ENNReal.ofReal (2 / s ^ 2) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hspos.le]
        simp [ENNReal.ofReal]
      _ < ENNReal.ofReal (1 / 8) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hPBr : μ.real B < 1 / 8 := ENNReal.toReal_lt_of_lt_ofReal hPB
  -- Paley–Zygmund through a pointwise bound
  set c : ℝ := Real.sqrt (8 * A) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 8 * A := Real.sq_sqrt (by positivity)
  have hpt : ∀ᵐ ω ∂μ, Y ω ≤ a / 2 + V ω / (2 * c) + B.indicator (fun _ => c / 2) ω := by
    filter_upwards [hpos, hYsq] with ω hω hωY
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB]
      have : Y ω ≤ V ω / (2 * c) + c / 2 := by
        rw [← hωY, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Y ω - c)]
      linarith
    · rw [Set.indicator_of_notMem hωB]
      have h1 : Y ω ≤ a / 2 := not_lt.1 hωB
      have h2 : 0 ≤ V ω / (2 * c) := by positivity
      linarith
  have hint2 : Integrable (fun ω => a / 2 + V ω / (2 * c) + B.indicator (fun _ => c / 2) ω) μ :=
    ((integrable_const _).add (hint.div_const _)).add
      ((integrable_const (c / 2)).indicator hBm)
  have hmono := integral_mono_ae hYint hint2 hpt
  have hRHS : ∫ ω, (a / 2 + V ω / (2 * c) + B.indicator (fun _ => c / 2) ω) ∂μ =
      a / 2 + A / (2 * c) + μ.real B * (c / 2) := by
    rw [integral_add (f := fun ω => a / 2 + V ω / (2 * c))
        (g := fun ω => B.indicator (fun _ => c / 2) ω)
        ((integrable_const _).add (hint.div_const _))
        ((integrable_const (c / 2)).indicator hBm),
      integral_add (f := fun _ => a / 2) (g := fun ω => V ω / (2 * c))
        (integrable_const _) (hint.div_const _), integral_const, integral_div,
      integral_indicator_const _ hBm]
    simp [smul_eq_mul, hAdef]
  rw [hRHS] at hmono
  have hAc : A / (2 * c) = c / 16 := by
    field_simp
    nlinarith [hc2]
  rw [hAc] at hmono
  have hac : a < c / 4 := by nlinarith
  have : a ^ 2 < A / 2 := by
    have : a ^ 2 < (c / 4) ^ 2 := pow_lt_pow_left₀ hac ha0 two_ne_zero
    nlinarith
  linarith

end BlockBand.DeterminantScore.NegativeSpread
