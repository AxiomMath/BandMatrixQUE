module

public import BlockBand.SourceProcess.Stochastic.SDE.SampledDoob
public import BlockBand.SourceProcess.Stochastic.SDE.Dyadic

/-!
# Continuous-time Doob `L²` maximal inequalities

Setting: an arbitrary measurable space `(Ω, m0)` with a finite measure `P` (no completeness, no
usual conditions), a filtration `𝓕 : Filtration ℝ≥0 m0`, a horizon `T : ℝ≥0`, and a
martingale `X : ℝ≥0 → Ω → E` (real Banach `E`) whose paths are `P`-a.s. right-continuous at
every `t ≤ T` (in particular, a.s. continuous paths suffice). No integrability beyond the
martingale property is assumed; right-hand sides may be `⊤`.

* `lintegral_iSup_sq_le_of_rightContinuous` / `lintegral_iSup_sq_le_of_continuous`:
  `∫⁻ ⨆_{t ≤ T} ‖X t‖ₑ² dP ≤ 4 ∫⁻ ‖X T‖ₑ² dP`.
* `measure_maximal_le_of_rightContinuous` / `measure_maximal_le_of_continuous` (real `X`):
  `λ² P(∃ t ≤ T, λ ≤ |X t|) ≤ ∫⁻ ‖X T‖ₑ² dP`, i.e. `P(sup_{t≤T} |X_t| ≥ λ) ≤ E X_T² / λ²`.

Proof: the dyadic samplings `dyadicTime T n` (discrete Doob in `SampledDoob`), monotone
convergence over the nested levels, and pathwise right-continuity
(`tendsto_dyadicUpper`) to identify the dyadic and continuum suprema.
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E]

omit m0 in
/-- Pathwise identification of the continuum supremum with the dyadic one. -/
theorem iSup_dyadic_eq_iSup {X : ℝ≥0 → Ω → E} {T : ℝ≥0} {ω : Ω}
    (hω : ∀ t ≤ T, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) :
    ⨆ n, ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2 = ⨆ t ≤ T, ‖X t ω‖ₑ ^ 2 := by
  refine le_antisymm (iSup_le fun n => iSup_le fun k => ?_) (iSup₂_le fun t ht => ?_)
  · exact le_iSup₂ (f := fun t (_ : t ≤ T) => ‖X t ω‖ₑ ^ 2) _ (dyadicTime_le T n k)
  · have hlim : Tendsto (fun n => ‖X (dyadicUpper T t n) ω‖ₑ ^ 2) atTop
        (𝓝 (‖X t ω‖ₑ ^ 2)) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((hω t ht).tendsto.comp (tendsto_dyadicUpper ht)))
    refine le_of_tendsto' hlim fun n => ?_
    exact le_trans (le_iSup (fun k => ‖X (dyadicTime T n k) ω‖ₑ ^ 2) (dyadicCeil T t n))
      (le_iSup (fun n => ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2) n)

omit m0 in
theorem iSup_dyadic_monotone (X : ℝ≥0 → Ω → E) (T : ℝ≥0) :
    Monotone fun n (ω : Ω) => ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2 := by
  refine monotone_nat_of_le_succ fun n ω => iSup_le fun k => ?_
  rw [← dyadicTime_succ T n k]
  exact le_iSup (fun k => ‖X (dyadicTime T (n + 1) k) ω‖ₑ ^ 2) (2 * k)

/-- **Continuous-time Doob `L²` maximal inequality** (right-continuous paths). -/
theorem lintegral_iSup_sq_le_of_rightContinuous [NormedSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0} {X : ℝ≥0 → Ω → E} (hX : Martingale X 𝓕 P)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, ∀ t ≤ T, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ‖X t ω‖ₑ ^ 2 ∂P ≤ 4 * ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := by
  have hmeas : ∀ n, Measurable fun ω => ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2 := fun n =>
    Measurable.iSup fun k =>
      (((hX.stronglyMeasurable _).mono (𝓕.le _)).enorm).pow_const 2
  calc ∫⁻ ω, ⨆ t ≤ T, ‖X t ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ⨆ n, ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc] with ω hω
        exact (iSup_dyadic_eq_iSup hω).symm
    _ = ⨆ n, ∫⁻ ω, ⨆ k, ‖X (dyadicTime T n k) ω‖ₑ ^ 2 ∂P :=
        lintegral_iSup hmeas (iSup_dyadic_monotone X T)
    _ ≤ 4 * ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := iSup_le fun n => by
        have h := lintegral_iSup_sampled_sq_le hX (dyadicTime T n) (dyadicTime_monotone T n)
          (2 ^ n) fun k hk => by rw [dyadicTime_of_le T n hk, dyadicTime_of_le T n le_rfl]
        rwa [dyadicTime_of_le T n le_rfl] at h

/-- **Continuous-time Doob `L²` maximal inequality** (continuous paths). -/
theorem lintegral_iSup_sq_le_of_continuous [NormedSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0} {X : ℝ≥0 → Ω → E} (hX : Martingale X 𝓕 P)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    ∫⁻ ω, ⨆ t ≤ T, ‖X t ω‖ₑ ^ 2 ∂P ≤ 4 * ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P :=
  lintegral_iSup_sq_le_of_rightContinuous hX T
    (hc.mono fun _ h _ _ => h.continuousAt.continuousWithinAt)

/-- From `l'² c ≤ C` for all `l' < l` to `l² c ≤ C` (finite `c`). -/
theorem sq_mul_le_of_forall_lt {l : ℝ≥0} {c C : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ l' < l, (l' : ℝ≥0∞) ^ 2 * c ≤ C) : (l : ℝ≥0∞) ^ 2 * c ≤ C := by
  rcases eq_or_ne l 0 with hl | hl
  · simp [hl]
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictMono_tendsto' (pos_of_ne_zero hl)
  have ht : Tendsto (fun n => (u n : ℝ≥0∞) ^ 2 * c) atTop (𝓝 ((l : ℝ≥0∞) ^ 2 * c)) :=
    ENNReal.Tendsto.mul_const (((ENNReal.continuous_pow 2).tendsto _).comp
      ((ENNReal.continuous_coe.tendsto _).comp hlim)) (Or.inr hc)
  exact le_of_tendsto' ht fun n => h _ (hu n).2

/-- **Continuous-time weak-type Doob `L²` inequality** (real martingale, right-continuous
paths): `λ² P(∃ t ≤ T, λ ≤ |X t|) ≤ ∫⁻ ‖X T‖ₑ²`. -/
theorem measure_maximal_le_of_rightContinuous [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ∀ t ≤ T, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) (l : ℝ≥0) :
    (l : ℝ≥0∞) ^ 2 * P {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|} ≤ ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := by
  refine sq_mul_le_of_forall_lt (measure_ne_top _ _) fun l' hl' => ?_
  let B : ℕ → Set Ω := fun n => {ω | ∃ k, (l' : ℝ) ≤ |X (dyadicTime T n k) ω|}
  have hBm : Monotone B := by
    refine monotone_nat_of_le_succ fun n ω ⟨k, hk⟩ => ⟨2 * k, ?_⟩
    rwa [dyadicTime_succ]
  have hsub : {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|} ≤ᵐ[P] (⋃ n, B n : Set Ω) := by
    filter_upwards [hc] with ω hω ⟨t, ht, hlt⟩
    have hlim : Tendsto (fun n => |X (dyadicUpper T t n) ω|) atTop (𝓝 |X t ω|) :=
      (continuous_abs.tendsto _).comp ((hω t ht).tendsto.comp (tendsto_dyadicUpper ht))
    have hev := hlim.eventually (lt_mem_nhds (lt_of_lt_of_le (NNReal.coe_lt_coe.2 hl') hlt))
    obtain ⟨n, hn⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨n, dyadicCeil T t n, hn.le⟩
  calc (l' : ℝ≥0∞) ^ 2 * P {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|}
      ≤ (l' : ℝ≥0∞) ^ 2 * P (⋃ n, B n) := mul_le_mul_right (measure_mono_ae hsub) _
    _ = ⨆ n, (l' : ℝ≥0∞) ^ 2 * P (B n) := by rw [hBm.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P := iSup_le fun n => by
        have h := measure_sampled_maximal_le hX (dyadicTime T n) (dyadicTime_monotone T n)
          (2 ^ n) (fun k hk => by rw [dyadicTime_of_le T n hk, dyadicTime_of_le T n le_rfl]) l'
        rwa [dyadicTime_of_le T n le_rfl] at h

/-- **Continuous-time weak-type Doob `L²` inequality** (real martingale, continuous paths). -/
theorem measure_maximal_le_of_continuous [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) (l : ℝ≥0) :
    (l : ℝ≥0∞) ^ 2 * P {ω | ∃ t ≤ T, (l : ℝ) ≤ |X t ω|} ≤ ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂P :=
  measure_maximal_le_of_rightContinuous hX T
    (hc.mono fun _ h _ _ => h.continuousAt.continuousWithinAt) l

end BlockBand.SourceProcess.Stochastic.SDE
