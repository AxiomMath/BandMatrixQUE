module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerY
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler limit agrees with a stopped solution before the stopping time

Pathwise uniqueness on the extension, in the form needed for the law argument.

Setting as in `EulerY` (hypotheses at every integer horizon `n`).
**`eulLim_eq_of_le`**: for every `t`, a.s. on `{t ≤ τ}`, `lim_m X^m_t = Y_t`
(Fatou with `X^m_t → eulLim t` a.s. and `E|X^m_{t∧τ} - Y_{t∧τ}|² → 0`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} {ξ : Ω → Fin d → ℝ}

theorem tendsto_const_div_two_pow (a b : ℝ) :
    Tendsto (fun m : ℕ => ENNReal.ofReal a * ENNReal.ofReal (b / 2 ^ m)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => b / 2 ^ m) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num)).const_mul b
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal (b / 2 ^ m)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h1
  simpa using ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)

/-- **The Euler limit is the stopped solution before `τ`.** -/
theorem eulLim_eq_of_le (hB : IsFiltrationBrownian P 𝓕 B) (c : LipCoef d)
    (hξ : Measurable[𝓕 0] ξ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ᵐ ω ∂P, Continuous fun t => Y t ω)
    {γY : Fin d → Fin d → ℝ × Ω → ℝ} (hγY : ∀ i l, IsBddPred 𝓕 (γY i l))
    (hγYe : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ i l, γY i l (r, ω) =
      (stopSet τ).indicator (fun p => c.σ (Y p.1.toNNReal p.2) i l) (r, ω))
    (hrep : ∀ n : ℕ, haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
      ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, Y (stopTime (τ ω) t) ω i = ξ ω i +
        ((∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
            (fun p => c.b (Y p.1.toNNReal p.2) i) (r, ω)) +
          hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (hγY i l)) t ω))
    (t : ℝ≥0) : ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤ τ ω → eulLim c ξ B t ω = Y t ω := by
  have hBm : ∀ t, Measurable (B t) := fun t => ((hB.adapted t).mono (𝓕.le t)).measurable
  have hE : ∀ m j, Measurable (eulE c m ξ B j) := fun m j =>
    (measurable_eulE c m (fun t => (hB.adapted t).measurable) hξ j).mono (𝓕.le _) le_rfl
  set n := ⌈(t : ℝ)⌉₊
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _
  have hG : MeasurableSet {ω | (t : WithTop ℝ≥0) ≤ τ ω} := measurableSet_le measurable_const
    hτ.measurable'
  set f : ℕ → Ω → ℝ≥0∞ := fun m => {ω | (t : WithTop ℝ≥0) ≤ τ ω}.indicator
    fun ω => ∑ i, ‖eulX c m ξ B t ω i - Y t ω i‖ₑ ^ 2
  have hfm : ∀ m, Measurable (f m) := fun m => Measurable.indicator
    (Finset.measurable_sum _ fun i _ => ((((measurable_pi_apply i).comp
      (measurable_eulX c m hBm (hE m) t)).sub ((measurable_pi_apply i).comp (hYm t))).enorm
        |>.pow_const 2)) hG
  have hbd : ∀ m, ∫⁻ ω, f m ω ∂P ≤
      ENNReal.ofReal (gronC n (eulLip c)) * ENNReal.ofReal (eulDelta c / 2 ^ m) := fun m => by
    refine le_trans (lintegral_mono fun ω => ?_) (lintegral_eulX_stop_sub_le hB c hξ n m hτ hYm
      hYc hγY (by filter_upwards [hγYe] with ω h r hr i l using h r hr.1 i l) (hrep n) t htn)
    simp only [f, indicator_apply, mem_ofPred_eq]
    split_ifs with h
    · rw [stopTime_of_le h]
    · exact zero_le
  have hlim : ∀ᵐ ω ∂P, liminf (fun m => f m ω) atTop = {ω | (t : WithTop ℝ≥0) ≤ τ ω}.indicator
      (fun ω => ∑ i, ‖eulLim c ξ B t ω i - Y t ω i‖ₑ ^ 2) ω := by
    filter_upwards [tendsto_eulLim hB c hξ t] with ω hω
    refine Tendsto.liminf_eq ?_
    simp only [f, indicator_apply, mem_ofPred_eq]
    split_ifs
    · refine tendsto_finsetSum _ fun i _ => ?_
      have h1 : Tendsto (fun m => eulX c m ξ B t ω i - Y t ω i) atTop
          (𝓝 (eulLim c ξ B t ω i - Y t ω i)) :=
        ((continuous_apply i).continuousAt.tendsto.comp hω).sub_const _
      exact (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
        (continuous_enorm.continuousAt.tendsto.comp h1)
    · exact tendsto_const_nhds
  have h0 : ∫⁻ ω, liminf (fun m => f m ω) atTop ∂P = 0 := by
    refine le_antisymm ((lintegral_liminf_le hfm).trans ?_) zero_le
    refine (liminf_le_liminf (Eventually.of_forall hbd)).trans ?_
    rw [(tendsto_const_div_two_pow _ _).liminf_eq]
  rw [lintegral_eq_zero_iff (Measurable.liminf hfm)] at h0
  filter_upwards [h0, hlim] with ω h1 h2 ht
  rw [h2] at h1
  simp only [Pi.zero_apply, indicator_apply, mem_ofPred_eq, ht, ite_true] at h1
  rw [Finset.sum_eq_zero_iff] at h1
  funext i
  have := h1 i (Finset.mem_univ i)
  rw [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, sub_eq_zero] at this
  exact this

end BlockBand.SourceProcess.Stochastic.Uniqueness
