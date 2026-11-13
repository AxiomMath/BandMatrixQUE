module
public import BlockBand.SourceProcess.Stochastic.SDE.ContinuousDoob
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Doob's weak `L²` inequality in modification form

Setting: `(Ω, m₀, P)` with `P` finite, a raw filtration `𝓕 : Filtration ℝ≥0 m₀`, a real
process `X` with `P`-a.s. continuous paths which has a martingale *modification* `M`
(`M t = X t` a.s. for each `t`; `M` itself need not have regular paths, and `X` need not be
adapted). This is the form available on raw filtrations, where continuous versions of
martingales cannot be chosen adapted.

`measure_maximal_le_of_modification`:
`λ² P(∃ t ≤ T, λ ≤ |X_t|) ≤ ∫⁻ ‖X_T‖ₑ² dP` (outer measure; no measurability of the event).
Proof: the dyadic argument of `SDE.ContinuousDoob` with the countably many dyadic values of
`X` replaced a.s. by those of `M`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.SourceProcess.Stochastic.SDE

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}

/-- **Weak-type Doob `L²` inequality for an a.s. continuous process with a martingale
modification.** -/
theorem measure_maximal_le_of_modification [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0}
    {X M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P) (hXM : ∀ t, M t =ᵐ[P] X t) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) (l : ℝ≥0) :
    (l : ℝ≥0∞) ^ 2 * P {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|} ≤ ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := by
  refine sq_mul_le_of_forall_lt (measure_ne_top _ _) fun l' hl' => ?_
  let B : ℕ → Set Ω := fun n => {ω | ∃ k, (l' : ℝ) ≤ |M (dyadicTime T n k) ω|}
  have hBm : Monotone B := by
    refine monotone_nat_of_le_succ fun n ω ⟨k, hk⟩ => ⟨2 * k, ?_⟩
    rwa [dyadicTime_succ]
  have hall : ∀ᵐ ω ∂P, ∀ n k, M (dyadicTime T n k) ω = X (dyadicTime T n k) ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hXM _
  have hsub : {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|} ≤ᵐ[P] (⋃ n, B n : Set Ω) := by
    filter_upwards [hc, hall] with ω hω hMX ⟨t, ht, hlt⟩
    have hlim : Tendsto (fun n => |X (dyadicUpper T t n) ω|) atTop (𝓝 |X t ω|) :=
      (continuous_abs.tendsto _).comp ((hω.tendsto t).comp
        ((tendsto_dyadicUpper ht).mono_right nhdsWithin_le_nhds))
    have hev := hlim.eventually (lt_mem_nhds (lt_of_lt_of_le (NNReal.coe_lt_coe.2 hl') hlt))
    obtain ⟨n, hn⟩ := hev.exists
    refine Set.mem_iUnion.2 ⟨n, dyadicCeil T t n, ?_⟩
    change (l' : ℝ) ≤ |M (dyadicUpper T t n) ω|
    rw [dyadicUpper, hMX]
    exact hn.le
  have hT : ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P :=
    lintegral_congr_ae ((hXM T).mono fun ω h => by simp [h])
  calc (l' : ℝ≥0∞) ^ 2 * P {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|}
      ≤ (l' : ℝ≥0∞) ^ 2 * P (⋃ n, B n) := mul_le_mul_right (measure_mono_ae hsub) _
    _ = ⨆ n, (l' : ℝ≥0∞) ^ 2 * P (B n) := by rw [hBm.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := iSup_le fun n => by
        have h := measure_sampled_maximal_le hM (dyadicTime T n) (dyadicTime_monotone T n)
          (2 ^ n) (fun k hk => by rw [dyadicTime_of_le T n hk, dyadicTime_of_le T n le_rfl]) l'
        rwa [dyadicTime_of_le T n le_rfl, hT] at h

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
