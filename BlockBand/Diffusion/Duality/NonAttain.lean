module
public import BlockBand.Diffusion.Duality.Lyapunov
public import BlockBand.Diffusion.Duality.Shift
public import BlockBand.Diffusion.Duality.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Non-attainment of the edges of the strip

**Headline (`stays_openStripFin`).** For every fixed time `q`, a.s.: if `Zf_q` lies in the
open strip `{y₀ > 0, 0 < y₁ < 1}`, then `Zf_r` lies in the open strip for all `r ≥ q`.
With `q = 0` and a deterministic start in the open strip, the base diffusion stays in the open
strip at all times.

Proof. Restart at `q` (`exists_martingale_stopped_shift`) and use the test `χ_m · stripLyap`
(`χ_m` a bump equal to `1` near the closed box `stripCBox m`), whose generator is `D₀` on the
box
(`mpGenerator_baseDrift_lyap`). On `A = {Zf_q ∈ stripBox n}` (`n ≤ m`), optional stopping at the
exit `τ_m` from `stripBox m` gives
`E[1_A (stripLyap(Z_{q+τ_m∧T}) − D₀ (τ_m∧T))] = E[1_A stripLyap(Zf_q)]`.
If the path leaves the open strip before `q + T` while its `y₀` stays below `N ≤ m`, the exit
point lies on an edge `y₀ = 1/m`, `y₁ = 1/m` or `y₁ = 1 − 1/m` of the box, where
`stripLyap ≥ log m` (`log_le_lyap_of_boundary`). Markov: that event has probability
`≤ (sup_{stripCBox n} stripLyap + |D₀| T)/log m → 0`. Countable union over `n, N, T`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission (shiftFiltration)
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
  {Zf : ℝ≥0 → Ω → Fin 2 → ℝ}

/-- The test `χ · stripLyap` for a bump `χ` supported in the open strip. -/
theorem isMPTest_mul_lyap {χ : (Fin 2 → ℝ) → ℝ} (hχ : IsMPTest openStripFin χ) :
    IsMPTest univ (fun y => χ y * stripLyap y) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hχ.2.1.mul_right, subset_univ _⟩
  by_cases hy : y ∈ openStripFin
  · exact hχ.1.contDiffAt.mul (contDiffAt_lyap hy)
  · have h0 : χ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hχ.2.2 h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with w hw
    simp [hw]

/-- The probability of leaving the strip from `stripBox n` before `q + T` with `y₀ < N`
vanishes. -/
theorem measure_leave_eq_zero (hZ : IsTestMPSolution Q 𝓖 (baseDrift D0) (baseCov D0) univ Zf)
    (q : ℝ≥0) {n : ℕ} (hn : 1 ≤ n) (N T : ℕ) :
    Q {ω | Continuous (fun r => Zf r ω) ∧ shiftProc Zf q 0 ω ∈ stripBox n ∧
      (∃ r ≤ (T : ℝ≥0), shiftProc Zf q r ω ∉ openStripFin) ∧
      ∀ r ≤ (T : ℝ≥0), shiftProc Zf q r ω 0 < N} = 0 := by
  set Zq := shiftProc Zf q with hZq
  set E := {ω | Continuous (fun r => Zf r ω) ∧ Zq 0 ω ∈ stripBox n ∧
      (∃ r ≤ (T : ℝ≥0), Zq r ω ∉ openStripFin) ∧ ∀ r ≤ (T : ℝ≥0), Zq r ω 0 < N} with hE
  obtain ⟨Kn, hKn0, hKn⟩ := exists_bound_lyap hn
  set c : ℝ := Kn + |D0| * T with hc
  -- the set `A`
  set A : Set Ω := {ω | Zq 0 ω ∈ stripBox n} with hA
  have hAm : MeasurableSet[shiftFiltration 𝓖 q 0] A :=
    (hZ.adapted (q + 0)) (isOpen_box n).measurableSet
  have hAm' : MeasurableSet A := (shiftFiltration 𝓖 q).le 0 _ hAm
  -- the bound for each large `m`
  have key : ∀ m : ℕ, n ≤ m → N ≤ m → 2 ≤ m → Q.real E ≤ c / Real.log m := by
    intro m hnm hNm hm2
    have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
    have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    obtain ⟨χ, V, hχ, hVo, hWV, hχ1⟩ := exists_bump isOpen_openStripFin (isInteriorDomain_box hm1)
    set f : (Fin 2 → ℝ) → ℝ := fun y => χ y * stripLyap y with hfdef
    have hf : IsMPTest univ f := isMPTest_mul_lyap hχ
    obtain ⟨M, hM, hMe⟩ := hZ.exists_martingale_stopped_shift isOpen_univ
      (continuous_baseDrift D0).continuousOn (continuous_baseCov D0).continuousOn hf
      (isOpen_box m) q
    have hgen : ∀ y ∈ closure (stripBox m), mpGenerator (baseDrift D0) (baseCov D0) f y = D0 :=
      fun y hy => by
        rw [mpGenerator_congr (eventuallyEq_mul_of_eq_one hVo hχ1 (hWV hy))]
        exact mpGenerator_baseDrift_lyap D0
          (cbox_subset_openStripFin hm1 (closure_box_subset m hy))
    -- localization: on continuous paths the stopped value is the `stripLyap` one
    have hloc : ∀ ω, Continuous (fun r => Zf r ω) → ∀ r,
        stoppedProcess (testCompensated f (mpGenerator (baseDrift D0) (baseCov D0) f) Zq)
          (exitTimeFrom (stripBox m) Zq) r ω =
        stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) r) ω) - stripLyap (Zq 0 ω) -
          D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) r : ℝ) := by
      intro ω hω r
      rw [stopped_testCompensated_eq (isOpen_box m) hWV (p := stripLyap) (q := fun _ => D0)
        (fun y hy => by simp [hfdef, hχ1 y hy]) hgen (continuous_shiftProc hω q) r]
      simp only [stoppedProcess_eq_stopTime, testCompensated, setIntegral_const, smul_eq_mul,
        Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
      ring
    -- the integral of `M_T` over `A` vanishes
    have hint0 : ∫ ω in A, M T ω ∂Q = 0 := by
      rw [← (hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) hAm)]
      rw [integral_congr_ae (ae_restrict_of_ae (hMe 0))]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
      simp [stoppedProcess_eq_stopTime, stopTime_zero, testCompensated]
    -- the function `G'`
    set gA : Ω → ℝ := fun ω => stripLyap (Zq 0 ω) with hgA
    have hgAm : AEStronglyMeasurable gA (Q.restrict A) :=
      aestronglyMeasurable_comp_continuousOn (Q := Q.restrict A)
        ((hZ.adapted (q + 0)).mono ((𝓖).le _) le_rfl) isOpen_openStripFin continuousOn_lyap
        ((ae_restrict_mem hAm').mono fun ω (hω : Zq 0 ω ∈ stripBox n) =>
          cbox_subset_openStripFin hn (closure_box_subset n (subset_closure hω)))
    have hgAb : ∀ᵐ ω ∂(Q.restrict A), ‖gA ω‖ ≤ Kn := (ae_restrict_mem hAm').mono fun ω hω => by
      have hy : Zq 0 ω ∈ closure (stripBox n) := subset_closure hω
      rw [Real.norm_eq_abs, abs_of_nonneg (lyap_nonneg (cbox_subset_openStripFin hn
        (closure_box_subset n hy)))]
      exact hKn _ (closure_box_subset n hy)
    have hgAi : Integrable gA (Q.restrict A) := Integrable.of_bound hgAm Kn hgAb
    set G : Ω → ℝ := fun ω => M T ω + gA ω + |D0| * T with hGdef
    have hMi : Integrable (M T) (Q.restrict A) := (hM.integrable T).restrict
    have hGi : Integrable G (Q.restrict A) := (hMi.add hgAi).add (integrable_const _)
    -- good paths
    have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Zf r ω) ∧
        M T ω = stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) -
          stripLyap (Zq 0 ω) -
          D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ) := by
      filter_upwards [hZ.continuous, hMe T] with ω h1 h2
      exact ⟨h1, h2.trans (hloc ω h1 T)⟩
    have hsub : ∀ ω, ω ∈ A → Continuous (fun r => Zf r ω) →
        Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω ∈ stripCBox m := fun ω hω hc =>
      closure_box_subset m (stop_mem_closure (isOpen_box m) (continuous_shiftProc hc q)
        (box_mono hn hnm hω) T)
    have hσ : ∀ ω, 0 ≤ (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ) ∧
        (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ) ≤ T := fun ω =>
      ⟨NNReal.coe_nonneg _, by exact_mod_cast stopTime_le _ _⟩
    have hGeq : ∀ ω, ω ∈ A → Continuous (fun r => Zf r ω) →
        M T ω = stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) -
          stripLyap (Zq 0 ω) -
          D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ) →
        stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) ≤ G ω := by
      intro ω hω hc he
      simp only [hGdef, hgA, he]
      have h1 : D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ) ≤ |D0| * T :=
        (le_abs_self _).trans (by
          rw [abs_mul, abs_of_nonneg (hσ ω).1]
          exact mul_le_mul_of_nonneg_left (hσ ω).2 (abs_nonneg _))
      linarith
    have hG0 : 0 ≤ᵐ[Q.restrict A] G := by
      filter_upwards [ae_restrict_mem hAm', ae_restrict_of_ae hgood] with ω hω h
      exact (lyap_nonneg (cbox_subset_openStripFin hm1 (hsub ω hω h.1))).trans
        (hGeq ω hω h.1 h.2)
    have hGint : ∫ ω, G ω ∂(Q.restrict A) ≤ c := by
      have e1 : ∫ ω, G ω ∂(Q.restrict A) = ∫ ω, (M T ω + gA ω) ∂(Q.restrict A) +
          ∫ _ω, (|D0| * T) ∂(Q.restrict A) := integral_add (hMi.add hgAi) (integrable_const _)
      have e2 : ∫ ω, (M T ω + gA ω) ∂(Q.restrict A) =
          ∫ ω, M T ω ∂(Q.restrict A) + ∫ ω, gA ω ∂(Q.restrict A) := integral_add hMi hgAi
      rw [e1, e2, hint0, zero_add, integral_const, smul_eq_mul]
      have h1 : ∫ ω, gA ω ∂(Q.restrict A) ≤ Kn := by
        have := norm_integral_le_of_norm_le (integrable_const Kn) hgAb
        rw [integral_const, smul_eq_mul] at this
        have hle : (Q.restrict A).real univ ≤ 1 := by
          rw [Measure.real, Measure.restrict_apply_univ]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        exact (le_abs_self _).trans (this.trans (by nlinarith))
      have h2 : (Q.restrict A).real univ * (|D0| * T) ≤ |D0| * T := by
        have hle : (Q.restrict A).real univ ≤ 1 := by
          rw [Measure.real, Measure.restrict_apply_univ]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        have : 0 ≤ |D0| * (T : ℝ) := by positivity
        nlinarith [measureReal_nonneg (μ := Q.restrict A) (s := univ)]
      rw [hc]; linarith
    have hmark := mul_meas_ge_le_integral_of_nonneg hG0 hGi (Real.log m)
    -- inclusion
    set S := {ω | Real.log m ≤ G ω} with hS
    have hEsub : E ⊆ (S ∩ A) ∪ {ω | ¬ (Continuous (fun r => Zf r ω) ∧
        M T ω = stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) -
          stripLyap (Zq 0 ω) -
          D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ))} := by
      intro ω hω
      by_cases hg : Continuous (fun r => Zf r ω) ∧
          M T ω = stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) -
            stripLyap (Zq 0 ω) -
            D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ)
      · left
        obtain ⟨hc, h0, ⟨r, hrT, hr⟩, hN⟩ := hω
        refine ⟨?_, h0⟩
        have hcq := continuous_shiftProc hc q
        have hτ : exitTimeFrom (stripBox m) Zq ω ≤ r := iInf₂_le r fun h =>
          hr (cbox_subset_openStripFin hm1 (closure_box_subset m (subset_closure h)))
        have hnot : Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω ∉ stripBox m := fun h =>
          absurd ((stop_mem_iff (isOpen_box m) hcq T).1 h)
            (not_lt.2 (hτ.trans (WithTop.coe_le_coe.2 hrT)))
        have hfar : Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω 0 < m :=
          lt_of_lt_of_le (hN _ (stopTime_le _ _)) (by exact_mod_cast hNm)
        exact (log_le_lyap_of_boundary hm1 (hsub ω h0 hc) hnot hfar).trans
          (hGeq ω h0 hc hg.2)
      · right; exact hg
    have hnull : Q {ω | ¬ (Continuous (fun r => Zf r ω) ∧
        M T ω = stripLyap (Zq (stopTime (exitTimeFrom (stripBox m) Zq ω) T) ω) -
          stripLyap (Zq 0 ω) -
          D0 * (stopTime (exitTimeFrom (stripBox m) Zq ω) T : ℝ))} = 0 :=
      ae_iff.1 hgood
    have hQE : Q E ≤ Q (S ∩ A) :=
      (measure_mono hEsub).trans ((measure_union_le _ _).trans (by rw [hnull, add_zero]))
    have hreal : Q.real E ≤ (Q.restrict A).real S := by
      rw [Measure.real, Measure.real, Measure.restrict_apply' hAm']
      exact ENNReal.toReal_mono (measure_ne_top _ _) hQE
    rw [le_div_iff₀ hlogm]
    have := hmark.trans hGint
    nlinarith [measureReal_nonneg (μ := Q) (s := E)]
  -- let `m → ∞`
  have hlim : Tendsto (fun m : ℕ => c / Real.log m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hle : Q.real E ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max (max n N) 2)] with m hm
    exact key m (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm))
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm))
      (le_trans (le_max_right _ _) hm)
  have h0 : Q.real E = 0 := le_antisymm hle measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0

/-- **DU2(a), restart form.** For each fixed `q`, a.s.: if `Zf_q` is in the open strip, the path
stays in the open strip at all later times. -/
theorem stays_openStripFin (hZ : IsTestMPSolution Q 𝓖 (baseDrift D0) (baseCov D0) univ Zf)
    (q : ℝ≥0) : ∀ᵐ ω ∂Q, Zf q ω ∈ openStripFin → ∀ r, q ≤ r → Zf r ω ∈ openStripFin := by
  have hnull : ∀ n N T : ℕ, Q {ω | Continuous (fun r => Zf r ω) ∧
      shiftProc Zf q 0 ω ∈ stripBox (n + 1) ∧
      (∃ r ≤ (T : ℝ≥0), shiftProc Zf q r ω ∉ openStripFin) ∧
      ∀ r ≤ (T : ℝ≥0), shiftProc Zf q r ω 0 < N} = 0 := fun n N T =>
    measure_leave_eq_zero hZ q (by omega) N T
  have hU := measure_iUnion_null fun n => measure_iUnion_null fun N =>
    measure_iUnion_null fun T => hnull n N T
  filter_upwards [hZ.continuous, measure_eq_zero_iff_ae_notMem.1 hU] with ω hc hω hq r hqr
  by_contra hr
  apply hω
  simp only [mem_iUnion]
  have hq' : shiftProc Zf q 0 ω ∈ openStripFin := by simpa using hq
  obtain ⟨n, hn1, hn⟩ := exists_box hq'
  obtain ⟨T, hT⟩ := exists_nat_ge ((r - q : ℝ≥0) : ℝ)
  have hcq := continuous_shiftProc hc q
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (T : ℝ≥0))).exists_bound_of_continuousOn
    (((continuous_apply 0).comp hcq).continuousOn)
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨n - 1, N, T, hc, by rwa [Nat.sub_add_cancel hn1], ⟨r - q, ?_, ?_⟩, fun r' hr' => ?_⟩
  · rw [← NNReal.coe_le_coe]; simpa using hT
  · simpa [add_tsub_cancel_of_le hqr] using hr
  · have := hB r' ⟨zero_le, hr'⟩
    rw [Real.norm_eq_abs] at this
    exact lt_of_le_of_lt ((le_abs_self _).trans this) hN

end BlockBand.Diffusion
