module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionMcKean

/-!
# McKean's argument: Itô, dominated convergence and Markov

* `lyapK_localized`: by (a2) the coordinates of `F + G_{s+·}` stopped at `ncRho` are a continuous
  semimartingale, a.s. in `simpleSet N` (fixed-time simple spectrum at `s > 0`); by (a1) applied to
  `lyap`, the compensated process `lyapK` has martingale modifications along a localizing sequence.
* `setIntegral_lyapK_eq_zero`: `∫_A K_T = 0` on `A = initGood G F s k` (an `𝓖_s`-event), by the
  martingale property at times `0 ≤ T` and dominated convergence on `A`.
* `mcKean_bound`: `log n · P(badSet G F s T k m) ≤ c(N, k, m)` for every `n ≥ max k 2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
  {s T : ℝ≥0} {n m k : ℕ}

/-- **Stopped Itô formula for the log-Vandermonde function** (from (a1), (a2)). -/
theorem lyapK_localized (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian) (hs : 0 < s) (hn : 0 < n) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ᵐ ω ∂Q, Tendsto (fun j => σ j ω) atTop (𝓝 ⊤)) ∧
      ∀ j, HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (stoppedProcess (lyapK G F s n m) (σ j)) := by
  have hY := isContinuousSemimartingale_hermVec hG hF s
  have hρ := isStoppingTime_ncRho hG hF s n m
  have hYρ := hStop (N * N) Ω Q (shiftFiltration 𝓖 s) _ _ _ hY _ hρ
  have hU : ∀ᵐ ω ∂Q, ∀ t, Ystop G F s n m t ω ∈ simpleSet N := by
    filter_upwards [simple_fixedTime hG hF hFh hs] with ω hω t
    show HasSimpleSpectrum N (vecHerm N (hermVec N _))
    rw [vecHerm_hermVec ((hFh ω).add (hG.hermitian _ ω))]
    exact simple_le_ncRho hG hn hω (untopA_min_le_rho t _)
  have hφc : ContDiffOn ℝ 2 (fun p : ℝ × (Fin (N * N) → ℝ) => lyap N p.2)
      (univ ×ˢ simpleSet N) :=
    fun p hp => ((contDiffAt_lyap hp.2).comp p contDiffAt_snd).contDiffWithinAt
  have hZ := hIto (N * N) Ω Q (shiftFiltration 𝓖 s) _ _ _ hYρ (simpleSet N) isOpen_simpleSet hU _
    (measurable_lyap.comp measurable_snd) hφc
  obtain ⟨σ, -, hσlim, hMM⟩ := hZ.localizing
  exact ⟨σ, hσlim, fun j => (hMM j).1 0⟩

/-- **The martingale identity on the good initial event**, with integrability. -/
theorem setIntegral_lyapK_eq_zero (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian) (hs : 0 < s) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hm : 0 < m) (T : ℝ≥0) :
    ∫ ω in initGood G F s k, lyapK G F s n m T ω ∂Q = 0 ∧
      Integrable (lyapK G F s n m T) (Q.restrict (initGood G F s k)) := by
  obtain ⟨σ, hσlim, hMM⟩ := lyapK_localized (m := m) hIto hStop hG hF hFh hs
    (lt_of_lt_of_le hk hkn)
  choose M hM hMe using hMM
  set A := initGood G F s k with hAdef
  set 𝓕 := shiftFiltration 𝓖 s
  have hA0 : MeasurableSet[𝓕 0] A := by
    show MeasurableSet[𝓖 (s + 0)] A
    rw [add_zero]; exact measurableSet_initGood hG hF s k
  have hAm : MeasurableSet A := 𝓕.le 0 A hA0
  have hK0 : ∀ j ω, stoppedProcess (lyapK G F s n m) (σ j) 0 ω = 0 := by
    intro j ω; rw [stoppedProcess_zero']; simp [lyapK]
  have hzero : ∀ j, ∫ ω in A, stoppedProcess (lyapK G F s n m) (σ j) T ω ∂Q = 0 := by
    intro j
    calc _ = ∫ ω in A, M j T ω ∂Q := integral_congr_ae (ae_restrict_of_ae (hMe j T).symm)
      _ = ∫ ω in A, M j 0 ω ∂Q := ((hM j).setIntegral_eq zero_le hA0).symm
      _ = ∫ ω in A, stoppedProcess (lyapK G F s n m) (σ j) 0 ω ∂Q :=
          integral_congr_ae (ae_restrict_of_ae (hMe j 0))
      _ = 0 := by simp [hK0]
  have haesm : ∀ j, AEStronglyMeasurable (stoppedProcess (lyapK G F s n m) (σ j) T) Q :=
    fun j => (((hM j).stronglyMeasurable T).mono (𝓕.le T)).aestronglyMeasurable.congr (hMe j T)
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun j => stoppedProcess (lyapK G F s n m) (σ j) T ω) atTop
      (𝓝 (lyapK G F s n m T ω)) := by
    filter_upwards [hσlim] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with j hj
    exact (stoppedProcess_eq_of_le (le_of_lt hj)).symm
  have hbd : ∀ j, ∀ᵐ ω ∂(Q.restrict A),
      ‖stoppedProcess (lyapK G F s n m) (σ j) T ω‖ ≤ kBound N k m n T := by
    intro j
    refine (ae_restrict_iff' hAm).mpr (Eventually.of_forall fun ω hω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_lyapK_le hG hFh hk hkn hm hω (untopA_min_le _ _)
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => kBound N k m n T)
    (fun j => (haesm j).restrict) (integrable_const _) hbd (ae_restrict_of_ae hlim)
  simp_rw [hzero] at hDCT
  refine ⟨(tendsto_nhds_unique hDCT tendsto_const_nhds), ?_⟩
  refine Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop haesm hlim).restrict
    (kBound N k m n T) ((ae_restrict_iff' hAm).mpr (Eventually.of_forall fun ω hω => ?_))
  rw [Real.norm_eq_abs]
  exact abs_lyapK_le hG hFh hk hkn hm hω le_rfl

/-- The constant of McKean's bound. -/
def mcKeanC (N k m : ℕ) : ℝ :=
  2 * (N : ℝ) ^ 2 * Real.log (sprR N k m) +
    (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (k : ℝ)))

/-- **McKean's bound**: `log n · P(collision from a good start) ≤ c(N, k, m)`. -/
theorem mcKean_bound (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian) (hs : 0 < s) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hm : 0 < m) (T : ℝ≥0) :
    Real.log n * Q.real (badSet G F s T k m) ≤ mcKeanC N k m := by
  obtain ⟨hint0, hint⟩ := setIntegral_lyapK_eq_zero hIto hStop hG hF hFh hs hk hkn hm T
  set A := initGood G F s k with hAdef
  have hAm : MeasurableSet A :=
    (𝓖.le s) _ (measurableSet_initGood hG hF s k)
  set c := mcKeanC N k m
  have hR := one_le_sprR (N := N) (m := m) hk
  have hlR := Real.log_nonneg hR
  have hLk : 0 ≤ (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (k : ℝ))) := by
    have : Real.log (1 / (k : ℝ)) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one (by positivity)).mpr (by exact_mod_cast hk))
    have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hc0 : 0 ≤ c := by
    have : 0 ≤ 2 * (N : ℝ) ^ 2 * Real.log (sprR N k m) := by positivity
    simp only [c, mcKeanC]; linarith
  set f : Ω → ℝ := fun ω => c - lyapK G F s n m T ω
  have hupA : ∀ ω ∈ A, lyapK G F s n m T ω ≤ c := by
    intro ω hω
    have h1 := lyapK_upper hG hFh hk hkn hm hω T
    have h2 := lyap_le hR (stopped_region hG hFh hk hkn hm hω T).2
    have : (N : ℝ) ^ 2 * Real.log (sprR N k m) ≤ 2 * (N : ℝ) ^ 2 * Real.log (sprR N k m) := by
      nlinarith [sq_nonneg (N : ℝ)]
    simp only [c, mcKeanC]; linarith
  have hf0 : 0 ≤ᵐ[Q.restrict A] f :=
    (ae_restrict_iff' hAm).mpr (Eventually.of_forall fun ω hω => by
      simp only [Pi.zero_apply, f]; linarith [hupA ω hω])
  have hfi : Integrable f (Q.restrict A) := (integrable_const c).sub hint
  have hMk := mul_meas_ge_le_integral_of_nonneg hf0 hfi (Real.log n)
  have hIf : ∫ ω, f ω ∂(Q.restrict A) ≤ c := by
    simp only [f]
    rw [integral_sub (integrable_const c) hint, integral_const, hint0, smul_eq_mul,
      measureReal_restrict_apply_univ, sub_zero]
    have : Q.real A ≤ 1 := measureReal_le_one
    nlinarith
  have hsub : badSet G F s T k m ⊆ {ω | Real.log n ≤ f ω} ∩ A := by
    intro ω hω
    refine ⟨?_, hω.1⟩
    have h1 := lyapK_upper hG hFh hk hkn hm hω.1 T
    have h2 := lyap_stopped_bad_le hG hFh hk hkn hm hω
    rw [one_div, Real.log_inv] at h2
    simp only [Set.mem_ofPred_eq, f, c, mcKeanC]
    linarith
  have hQ : Q.real (badSet G F s T k m) ≤ (Q.restrict A).real {ω | Real.log n ≤ f ω} :=
    (measureReal_mono hsub).trans
      (ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_restrict_apply _ _))
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  calc Real.log n * Q.real (badSet G F s T k m)
      ≤ Real.log n * (Q.restrict A).real {ω | Real.log n ≤ f ω} :=
        mul_le_mul_of_nonneg_left hQ hlog
    _ ≤ _ := hMk
    _ ≤ c := hIf

end BlockBand.SourceProcess.Stochastic.Dyson
