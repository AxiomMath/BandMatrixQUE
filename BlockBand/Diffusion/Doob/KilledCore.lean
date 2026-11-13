module
public import BlockBand.Diffusion.Duality.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The windowed duality identity for a killed path

**Main result (`dk_window_identity_killed`).** For a time window `χ` (`IsTimeWindow χ c c₂`,
`s < c < c₂ < t`), with `F_χ(ω) = ∫_{(0,t]} χ'(r) u(r, Z_r(ω)) dr`, the function
`u(t, Z_t) - F_χ` is a.e. strongly measurable and `∫_A (u(t, Z_t) - F_χ) dQ = 0` for every
`A ∈ 𝓖_s`.

Proof: that of `window_identity` with `U = O`, except for the
pathwise limit. On a good path with `ζ > t` it is the argument of `window_identity`. If `ζ ≤ t` the
space-time path leaves the window domain at time `ζ` (its spatial part reaches `κ ∉ O`), the
exit times of the exhaustion tend to `ζ`, and the stopped values tend to `u(t, Z_t) - F_χ`
because `u(r, ·) → 0` at `κ` (the bound `L |x - κ|`) and the integrand of `F_χ` vanishes after
`ζ`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

variable {d : ℕ}

/-- `χ' = 0` up to the start of the window (including the endpoint `c`). -/
theorem IsTimeWindow.deriv_eq_zero_of_le {χ : ℝ → ℝ} {c c₂ : ℝ} (h : IsTimeWindow χ c c₂)
    {r : ℝ} (hr : r ≤ c) : deriv χ r = 0 := by
  rcases hr.lt_or_eq with hr | hr
  · exact h.deriv_eq_zero_of_lt hr
  · subst hr
    have h1 : Tendsto (deriv χ) (𝓝[<] r) (𝓝 (deriv χ r)) :=
      (h.continuous_deriv.tendsto r).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv χ) (𝓝[<] r) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun q hq =>
        (h.deriv_eq_zero_of_lt hq).symm)
    exact tendsto_nhds_unique h1 h2

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {O : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ} {c c₂ : ℝ} {χ : ℝ → ℝ}
  {u : ℝ × (Fin d → ℝ) → ℝ}

/-- **The windowed duality identity for a killed path**: `∫_A (u(t, Z_t) - F_χ) dQ = 0` for
`A ∈ 𝓖_s`. -/
theorem dk_window_identity_killed (hZ : IsMPSolutionOn Q 𝓖 b a O Z) (hO : IsOpen O)
    (hb : ContinuousOn b O) (ha : ContinuousOn a O) {s t : ℝ≥0}
    (hsc : (s : ℝ) < c) (hct : c₂ < t) (hχ : IsTimeWindow χ c c₂)
    (hu2 : ContDiffOn ℝ 2 u (Ioo (s : ℝ) t ×ˢ O))
    (hpde : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, stGen b a u p = 0)
    (huc : ∀ x ∈ O, ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((t : ℝ), x))
    {κ : Fin d → ℝ} (hκ : κ ∉ O) (hu0 : ∀ r, u (r, κ) = 0) {Lc : ℝ}
    (hlin : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ Lc * ‖p.2 - κ‖)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ C) {ζ : Ω → ℝ≥0∞}
    (hpath : ∀ᵐ ω ∂Q, (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) ∧
      ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ) :
    AEStronglyMeasurable (fun ω => u ((t : ℝ), Z t ω) - windowAvg χ u Z t ω) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, (u ((t : ℝ), Z t ω) - windowAvg χ u Z t ω) ∂Q = 0 := by
  have hcc : c ≤ c₂ := hχ.le
  have hst : s ≤ t := by
    have : (s : ℝ) < t := by linarith
    exact_mod_cast this.le
  have hst' : s < t := by
    have : (s : ℝ) < t := by linarith
    exact_mod_cast this
  have hCo : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, |u p| ≤ C := fun p hp =>
    hC p ⟨Ioo_subset_Ioc_self hp.1, hp.2⟩
  set V := windowDomain O O c s t with hVdef
  have hV : IsOpen V := isOpen_windowDomain hO hO
  have hVU : ∀ y ∈ V, Fin.tail y ∈ O := fun y hy => tail_mem_of_windowDomain subset_rfl hy
  have hY := IsMPSolutionOn.spaceTime hZ hO hb ha hVU
  set φ := cutFun χ u with hφdef
  have hφ : ContDiffOn ℝ 2 φ V := contDiffOn_cutFun hχ hO hu2
  set Y := stProc Z with hYdef
  set L := mpGenerator (stDrift b) (stCov a) φ with hLdef
  set X : ℝ≥0 → Ω → ℝ := fun r ω => φ (Y r ω) - φ (Y 0 ω) -
    ∫ r' in Ioc (0 : ℝ) r, L (Y r'.toNNReal ω) with hXdef
  have hWd : ∀ m, IsInteriorDomain (exhaust V m) V := fun m =>
    ⟨isOpen_exhaust m, isCompact_closure_exhaust m, closure_exhaust_subset_U m⟩
  have hMart : ∀ m : ℕ, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ r,
      M r =ᵐ[Q] stoppedProcess X (exitTimeFrom (exhaust V m) Y) r := fun m =>
    GramUniqueness.martingaleProblemItoU_holds (d + 1) Ω Q 𝓖 _ _ V hV (continuousOn_stDrift hb hVU)
      (continuousOn_stCov ha hVU) Y hY φ hφ (exhaust V m) (hWd m)
  choose M hM hMe using hMart
  obtain ⟨K, hK0, hK⟩ := hχ.exists_bound
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun m => exitTimeFrom (exhaust V m) Y with hτdef
  set G : ℕ → Ω → ℝ := fun m ω => stoppedProcess X (τ m) t ω with hGdef
  set H : Ω → ℝ := fun ω => u ((t : ℝ), Z t ω) - windowAvg χ u Z t ω with hHdef
  -- at time `s` the stopped process vanishes identically
  have hF1 : ∀ m ω, stoppedProcess X (τ m) s ω = 0 := fun m ω => by
    rw [stoppedProcess_eq_stopTime]
    set σ := stopTime (τ m ω) s
    have hσ : (σ : ℝ) < c := lt_of_le_of_lt (NNReal.coe_le_coe.2 (stopTime_le _ _)) hsc
    have h0 : (0 : ℝ) < c := lt_of_le_of_lt (NNReal.coe_nonneg s) hsc
    simp only [hXdef]
    rw [hφdef, cutFun_eq_zero hχ (by simpa [hYdef] using hσ.le),
      cutFun_eq_zero hχ (by simpa [hYdef] using h0.le)]
    rw [setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_]
    · ring
    · refine mpGenerator_cutFun_of_lt b a hχ ?_
      simp only [hYdef, stProc_zero]
      rw [Real.coe_toNNReal _ hr.1.le]
      exact lt_of_le_of_lt hr.2 hσ
  -- the stopped values integrate to zero on `𝓖_s`-sets
  have hF2 : ∀ m (A : Set Ω), MeasurableSet[𝓖 s] A → ∫ ω in A, G m ω ∂Q = 0 := by
    intro m A hA
    have e1 : ∫ ω in A, G m ω ∂Q = ∫ ω in A, M m t ω ∂Q :=
      integral_congr_ae (EventuallyEq.symm (ae_restrict_of_ae (hMe m t)))
    have e2 : ∫ ω in A, M m s ω ∂Q = 0 := by
      rw [integral_congr_ae (ae_restrict_of_ae (hMe m s))]
      simp only [show ∀ ω, stoppedProcess X (exitTimeFrom (exhaust V m) Y) s ω = 0 from hF1 m,
        integral_zero]
    rw [e1, ← (hM m).setIntegral_eq hst hA, e2]
  -- measurability of the stopped values
  have hF6 : ∀ m, AEStronglyMeasurable (G m) Q := fun m =>
    (((hM m).1 t).mono (𝓖.le t)).aestronglyMeasurable.congr (hMe m t)
  -- the good paths
  have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Z r ω) ∧
      (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) ∧ ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ := by
    filter_upwards [hZ.continuous, hpath] with ω h1 h2 using ⟨h1, h2⟩
  -- pathwise facts
  have hpw : ∀ ω, Continuous (fun r => Z r ω) →
      (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) → (∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ) →
      Tendsto (fun m => G m ω) atTop (𝓝 (H ω)) ∧ ∀ m, |G m ω| ≤ C + K * C * t := by
    intro ω hZc hZO hZκ
    have hYc : Continuous fun r => Y r ω := continuous_stProc hZc
    have hclos : ∀ m, ∀ r ∈ Ioc (0 : ℝ) (stopTime (τ m ω) t), Y r.toNNReal ω ∈ V :=
      fun m r hr =>
        closure_exhaust_subset_U m ((stopped_path_mem_closure (isOpen_exhaust m) hYc t).1 r hr)
    have hint : ∀ m, ∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t), L (Y r'.toNNReal ω) =
        ∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t), deriv χ r' * u (r', Z r'.toNNReal ω) :=
      fun m => setIntegral_congr_fun measurableSet_Ioc fun r hr => by
        rw [hLdef, mpGenerator_cutFun b a hχ hO hu2 hpde (hclos m r hr), cutGen]
        simp only [hYdef, stProc_zero, stEquiv_stProc, Real.coe_toNNReal _ hr.1.le]
    have hφ0 : φ (Y 0 ω) = 0 := cutFun_eq_zero hχ (by
      simp only [hYdef, stProc_zero, NNReal.coe_zero]
      linarith [NNReal.coe_nonneg s])
    have hGe : ∀ m, G m ω = φ (Y (stopTime (τ m ω) t) ω) -
        ∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t), deriv χ r' * u (r', Z r'.toNNReal ω) :=
      fun m => by
        simp only [hGdef, stoppedProcess_eq_stopTime, hXdef, hφ0, sub_zero, hint m]
    -- the bound, when the path starts in the window domain
    have hbound : Y 0 ω ∈ V → ∀ m, |G m ω| ≤ C + K * C * t := by
      intro hY0 m
      have hend : Y (stopTime (τ m ω) t) ω ∈ V := by
        rcases (stopped_path_mem_closure (isOpen_exhaust m) hYc t).2 with h | ⟨h, -⟩
        · rw [h]; exact hY0
        · exact closure_exhaust_subset_U m h
      rw [hGe m]
      have h1 := abs_cutFun_le hχ hC0 hCo hend
      have h2 : |∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t), L (Y r'.toNNReal ω)| ≤ K * C * t :=
        abs_integral_stop_le (isOpen_exhaust m) hYc (g := L) (mul_nonneg hK0 hC0)
          (fun y hy => by
            rw [hLdef, mpGenerator_cutFun b a hχ hO hu2 hpde (closure_exhaust_subset_U m hy)]
            exact abs_cutGen_le hχ hK hC0 hCo (closure_exhaust_subset_U m hy)) le_rfl
      rw [hint m] at h2
      calc _ ≤ |φ (Y (stopTime (τ m ω) t) ω)| + |∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t),
            deriv χ r' * u (r', Z r'.toNNReal ω)| := abs_sub _ _
        _ ≤ C + K * C * t := add_le_add h1 h2
    by_cases hζt : (t : ℝ≥0∞) < ζ ω
    · -- the path survives up to `t`: the argument of `window_identity`
      have hZU : ∀ r ≤ t, Z r ω ∈ O := fun r hr =>
        hZO r (lt_of_le_of_lt (by exact_mod_cast hr) hζt)
      have hin : ∀ r < t, Y r ω ∈ V := fun r hr => by
        by_cases hrc : (r : ℝ) < c
        · exact Or.inl ⟨hrc, by simpa [hYdef] using hZU r hr.le⟩
        · push Not at hrc
          refine Or.inr ⟨⟨by simpa [hYdef] using lt_of_lt_of_le hsc hrc,
            by simpa [hYdef] using hr⟩, by simpa [hYdef] using hZU r hr.le⟩
      have hout : Y t ω ∉ V := by
        rintro (h | h)
        · have : (t : ℝ) < c := by simpa [hYdef] using h.1
          linarith
        · have : (t : ℝ) < t := by simpa [hYdef] using h.1.2
          exact lt_irrefl _ this
      have hY0 : Y 0 ω ∈ V := hin 0 (lt_of_le_of_lt zero_le hst')
      obtain ⟨hτ1, hτ2⟩ := exit_exhaust_facts hV hYc hin hout
      have hσlim : Tendsto (fun m => stopTime (τ m ω) t) atTop (𝓝 t) :=
        tendsto_stopTime_of_facts hτ1 hτ2
      have hσlimR : Tendsto (fun m => (stopTime (τ m ω) t : ℝ)) atTop (𝓝 (t : ℝ)) :=
        (NNReal.continuous_coe.tendsto t).comp hσlim
      have hev1 : ∀ᶠ m in atTop, c₂ < (stopTime (τ m ω) t : ℝ) :=
        hσlimR.eventually_const_lt hct
      refine ⟨?_, hbound hY0⟩
      have hZt : Z t ω ∈ O := hZU t le_rfl
      have hp : Tendsto (fun m => ((stopTime (τ m ω) t : ℝ), Z (stopTime (τ m ω) t) ω)) atTop
          (𝓝[Ioc (s : ℝ) t ×ˢ O] ((t : ℝ), Z t ω)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hσlimR.prodMk_nhds ((hZc.tendsto t).comp hσlim), ?_⟩
        filter_upwards [hev1] with m hm
        have hsσ : (s : ℝ) < stopTime (τ m ω) t := by linarith
        exact ⟨⟨hsσ, NNReal.coe_le_coe.2 (stopTime_le _ _)⟩, hZU _ (stopTime_le _ _)⟩
      have hlim := ((huc _ hZt).tendsto.comp hp).sub_const (windowAvg χ u Z t ω)
      refine hlim.congr' ?_
      filter_upwards [hev1] with m hm
      rw [hGe m]
      simp only [Function.comp]
      congr 1
      · rw [hφdef, cutFun_apply, hχ.one _ (by simpa [hYdef] using hm.le), one_mul]
        simp [hYdef]
      · rw [windowAvg, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
          measurableSet_Ioc.nullMeasurableSet
          (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (stopTime_le _ _)))
          (Eventually.of_forall fun r hr => ?_)]
        rw [hχ.deriv_eq_zero_of_gt, zero_mul]
        have : ¬ r ≤ (stopTime (τ m ω) t : ℝ) := fun h => hr.2 ⟨hr.1.1, h⟩
        push Not at this
        linarith
    · -- the path is killed at `ζ ≤ t`
      push Not at hζt
      obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ≥0, ζ ω = T₀ :=
        ⟨(ζ ω).toNNReal, (ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hζt)).symm⟩
      rw [hT₀] at hζt hZO hZκ
      have hT₀t : T₀ ≤ t := by exact_mod_cast hζt
      have hT₀tR : (T₀ : ℝ) ≤ t := by exact_mod_cast hT₀t
      have hZO' : ∀ r < T₀, Z r ω ∈ O := fun r hr => hZO r (by exact_mod_cast hr)
      have hZκ' : ∀ r : ℝ≥0, T₀ ≤ r → Z r ω = κ := fun r hr => hZκ r (by exact_mod_cast hr)
      have hin : ∀ r < T₀, Y r ω ∈ V := fun r hr => by
        by_cases hrc : (r : ℝ) < c
        · exact Or.inl ⟨hrc, by simpa [hYdef] using hZO' r hr⟩
        · push Not at hrc
          have hrt : (r : ℝ) < t := lt_of_lt_of_le (by exact_mod_cast hr) hT₀tR
          refine Or.inr ⟨⟨by simpa [hYdef] using lt_of_lt_of_le hsc hrc,
            by simpa [hYdef] using hrt⟩, by simpa [hYdef] using hZO' r hr⟩
      have hout : Y T₀ ω ∉ V := by
        have hκ' : Z T₀ ω ∉ O := by rw [hZκ' T₀ le_rfl]; exact hκ
        rintro (h | h)
        · exact hκ' (by simpa [hYdef] using h.2)
        · exact hκ' (by simpa [hYdef] using h.2)
      obtain ⟨hτ1, hτ2⟩ := exit_exhaust_facts hV hYc hin hout
      have hστ : ∀ m, stopTime (τ m ω) t = stopTime (τ m ω) T₀ := fun m => by
        obtain ⟨σ, hσ⟩ : ∃ σ : ℝ≥0, τ m ω = σ := WithTop.ne_top_iff_exists.1
          (ne_top_of_le_ne_top WithTop.coe_ne_top (hτ1 m)) |>.imp fun _ h => h.symm
        have hσT : σ ≤ T₀ := WithTop.coe_le_coe.1 (hσ ▸ hτ1 m)
        rw [hσ, stopTime_coe, stopTime_coe, min_eq_right (hσT.trans hT₀t), min_eq_right hσT]
      have hσlim : Tendsto (fun m => stopTime (τ m ω) t) atTop (𝓝 T₀) := by
        simp only [hστ]; exact tendsto_stopTime_of_facts hτ1 hτ2
      have hσlimR : Tendsto (fun m => (stopTime (τ m ω) t : ℝ)) atTop (𝓝 (T₀ : ℝ)) :=
        (NNReal.continuous_coe.tendsto T₀).comp hσlim
      have hσT : ∀ m, stopTime (τ m ω) t ≤ T₀ := fun m => by
        rw [hστ m]; exact stopTime_le _ _
      -- the integrand of `F_χ` vanishes after `ζ` and before `c`
      set f : ℝ → ℝ := fun r => deriv χ r * u (r, Z r.toNNReal ω) with hfdef
      have hfT : ∀ r : ℝ, (T₀ : ℝ) ≤ r → f r = 0 := fun r hr => by
        have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg T₀).trans hr
        have : T₀ ≤ r.toNNReal := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr
        simp only [hfdef, hZκ' _ this, hu0, mul_zero]
      have hfc : ∀ r : ℝ, r ≤ c → f r = 0 := fun r hr => by
        simp only [hfdef, hχ.deriv_eq_zero_of_le hr, zero_mul]
      have hH : H ω = -∫ r in Ioc (0 : ℝ) t, f r := by
        simp only [hHdef, windowAvg, hZκ' t hT₀t, hu0, zero_sub, hfdef]
      by_cases hTc : (T₀ : ℝ) ≤ c
      · -- killed before the window: everything vanishes
        have hf0 : ∀ r, f r = 0 := fun r => by
          rcases le_total r c with h | h
          · exact hfc r h
          · exact hfT r (hTc.trans h)
        have hG0 : ∀ m, G m ω = 0 := fun m => by
          rw [hGe m]
          have hσc : (stopTime (τ m ω) t : ℝ) ≤ c :=
            (NNReal.coe_le_coe.2 (hσT m)).trans hTc
          rw [hφdef, cutFun_eq_zero hχ (by simpa [hYdef] using hσc)]
          rw [setIntegral_eq_zero_of_forall_eq_zero fun r _ => hf0 r, sub_zero]
        have hH0 : H ω = 0 := by rw [hH]; simp [hf0]
        refine ⟨?_, fun m => by rw [hG0 m, abs_zero]; positivity⟩
        rw [hH0]
        exact tendsto_const_nhds.congr fun m => (hG0 m).symm
      · -- killed inside or after the window
        push Not at hTc
        have hY0 : Y 0 ω ∈ V := hin 0 (by
          have : (0 : ℝ) < T₀ := lt_of_le_of_lt (le_of_lt (lt_of_le_of_lt
            (NNReal.coe_nonneg s) hsc)) hTc
          exact_mod_cast this)
        refine ⟨?_, hbound hY0⟩
        have hev1 : ∀ᶠ m in atTop, c < (stopTime (τ m ω) t : ℝ) :=
          hσlimR.eventually_const_lt hTc
        have hendO : ∀ m, Z (stopTime (τ m ω) t) ω ∈ O := fun m => by
          have hend : Y (stopTime (τ m ω) t) ω ∈ V := by
            rcases (stopped_path_mem_closure (isOpen_exhaust m) hYc t).2 with h | ⟨h, -⟩
            · rw [h]; exact hY0
            · exact closure_exhaust_subset_U m h
          simpa [hYdef] using hVU _ hend
        -- the boundary term tends to `0`
        have hZlim : Tendsto (fun m => Z (stopTime (τ m ω) t) ω) atTop (𝓝 κ) := by
          rw [← hZκ' T₀ le_rfl]; exact (hZc.tendsto T₀).comp hσlim
        have hb1 : Tendsto (fun m => φ (Y (stopTime (τ m ω) t) ω)) atTop (𝓝 0) := by
          have hn : Tendsto (fun m => Lc * ‖Z (stopTime (τ m ω) t) ω - κ‖) atTop (𝓝 0) := by
            have := ((continuous_norm.comp (continuous_sub_right κ)).tendsto κ).comp hZlim
            simpa using this.const_mul Lc
          refine squeeze_zero_norm' ?_ hn
          filter_upwards [hev1] with m hm
          rw [hφdef, cutFun_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ.nonneg _)]
          have hmem : ((stopTime (τ m ω) t : ℝ), Z (stopTime (τ m ω) t) ω) ∈
              Ioc (s : ℝ) t ×ˢ O :=
            ⟨⟨by linarith, NNReal.coe_le_coe.2 (stopTime_le _ _)⟩, hendO m⟩
          have h1 := hlin _ hmem
          simp only [hYdef, stEquiv_stProc, stProc_zero] at h1 ⊢
          calc χ (stopTime (τ m ω) t) * |u ((stopTime (τ m ω) t : ℝ), Z (stopTime (τ m ω) t) ω)|
              ≤ 1 * (Lc * ‖Z (stopTime (τ m ω) t) ω - κ‖) :=
                mul_le_mul (hχ.le_one _) h1 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        -- the integral term converges
        have hfb : ∀ r ∈ Ioc (0 : ℝ) T₀, |f r| ≤ K * C := fun r hr => by
          by_cases hrc : r ≤ c
          · rw [hfc r hrc, abs_zero]; exact mul_nonneg hK0 hC0
          · push Not at hrc
            rcases hr.2.lt_or_eq with hrT | hrT
            · have hr0 : (0 : ℝ) ≤ r := hr.1.le
              have hmem : (r, Z r.toNNReal ω) ∈ Ioc (s : ℝ) t ×ˢ O := by
                refine ⟨⟨by linarith, by linarith⟩, hZO' _ ?_⟩
                rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hrT
              rw [hfdef, abs_mul]
              exact mul_le_mul (hK r) (hC _ hmem) (abs_nonneg _) hK0
            · rw [hfT r hrT.ge, abs_zero]; exact mul_nonneg hK0 hC0
        have hfcont : ContinuousOn f (Ioo (s : ℝ) T₀) := by
          have hpc : ContinuousOn (fun r : ℝ => (r, Z r.toNNReal ω)) (Ioo (s : ℝ) T₀) :=
            (continuous_id.prodMk (hZc.comp continuous_real_toNNReal)).continuousOn
          refine hχ.continuous_deriv.continuousOn.mul (hu2.continuousOn.comp hpc fun r hr => ?_)
          have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg s).trans hr.1.le
          refine ⟨⟨hr.1, lt_of_lt_of_le hr.2 hT₀tR⟩, hZO' _ ?_⟩
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr.2
        have hfind : ∀ r ∈ Ioc (0 : ℝ) T₀, f r = (Ioo (s : ℝ) T₀).indicator f r := fun r hr => by
          by_cases hrs : r ∈ Ioo (s : ℝ) T₀
          · rw [indicator_of_mem hrs]
          · rw [indicator_of_notMem hrs]
            simp only [mem_Ioo, not_and_or, not_lt] at hrs
            rcases hrs with h | h
            · exact hfc r (h.trans hsc.le)
            · exact hfT r h
        have hfi : IntegrableOn f (Ioc (0 : ℝ) T₀) := by
          have h1 : IntegrableOn f (Ioo (s : ℝ) T₀) := by
            refine ⟨hfcont.aestronglyMeasurable measurableSet_Ioo,
              .restrict_of_bounded (C := K * C) measure_Ioo_lt_top ?_⟩
            refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr => ?_)
            rw [Real.norm_eq_abs]
            exact hfb r ⟨lt_of_le_of_lt (NNReal.coe_nonneg s) hr.1, hr.2.le⟩
          have h2 : IntegrableOn ((Ioo (s : ℝ) T₀).indicator f) (Ioc (0 : ℝ) T₀) :=
            (h1.integrable_indicator measurableSet_Ioo).integrableOn
          exact h2.congr_fun (fun r hr => (hfind r hr).symm) measurableSet_Ioc
        have htT : ∫ r in Ioc (0 : ℝ) t, f r = ∫ r in Ioc (0 : ℝ) T₀, f r := by
          refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
            measurableSet_Ioc.nullMeasurableSet (Ioc_subset_Ioc_right hT₀tR)
            (Eventually.of_forall fun r hr => ?_)
          have : ¬ r ≤ (T₀ : ℝ) := fun h => hr.2 ⟨hr.1.1, h⟩
          push Not at this
          exact hfT r this.le
        have hb2 : Tendsto (fun m => ∫ r in Ioc (0 : ℝ) (stopTime (τ m ω) t), f r) atTop
            (𝓝 (∫ r in Ioc (0 : ℝ) T₀, f r)) := by
          have hdiff : ∀ m, (∫ r in Ioc (0 : ℝ) T₀, f r) -
              ∫ r in Ioc (0 : ℝ) (stopTime (τ m ω) t), f r =
                ∫ r in Ioc ((stopTime (τ m ω) t : ℝ)) T₀, f r := fun m => by
            have hle : (stopTime (τ m ω) t : ℝ) ≤ T₀ := NNReal.coe_le_coe.2 (hσT m)
            have hu : Ioc (0 : ℝ) T₀ = Ioc 0 (stopTime (τ m ω) t : ℝ) ∪
                Ioc (stopTime (τ m ω) t : ℝ) T₀ :=
              (Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg _) hle).symm
            rw [hu, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
              (hfi.mono_set (Ioc_subset_Ioc_right hle))
              (hfi.mono_set (Ioc_subset_Ioc_left (NNReal.coe_nonneg _)))]
            ring
          rw [tendsto_iff_norm_sub_tendsto_zero]
          have hlim0 : Tendsto (fun m => K * C * ((T₀ : ℝ) - stopTime (τ m ω) t)) atTop
              (𝓝 0) := by
            have := (tendsto_const_nhds (x := (T₀ : ℝ))).sub hσlimR
            simpa using this.const_mul (K * C)
          refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim0
          rw [norm_sub_rev, hdiff m]
          have hle : (stopTime (τ m ω) t : ℝ) ≤ T₀ := NNReal.coe_le_coe.2 (hσT m)
          have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f)
            (s := Ioc ((stopTime (τ m ω) t : ℝ)) T₀) measure_Ioc_lt_top (C := K * C)
            (fun r hr => by
              rw [Real.norm_eq_abs]
              exact hfb r ⟨lt_of_le_of_lt (NNReal.coe_nonneg _) hr.1, hr.2⟩)
          rw [Real.volume_real_Ioc_of_le hle] at h
          exact h
        have hlim := hb1.sub hb2
        rw [zero_sub] at hlim
        rw [hH, htT]
        refine hlim.congr fun m => ?_
        rw [hGe m]
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun m => G m ω) atTop (𝓝 (H ω)) :=
    hgood.mono fun ω h => (hpw ω h.1 h.2.1 h.2.2).1
  have hbd : ∀ m, ∀ᵐ ω ∂Q, ‖G m ω‖ ≤ C + K * C * t := fun m =>
    hgood.mono fun ω h => by rw [Real.norm_eq_abs]; exact (hpw ω h.1 h.2.1 h.2.2).2 m
  have hHm : AEStronglyMeasurable H Q := aestronglyMeasurable_of_tendsto_ae atTop hF6 hlim
  refine ⟨hHm, fun A hA => ?_⟩
  have hT := tendsto_integral_of_dominated_convergence (μ := Q.restrict A)
    (fun _ => C + K * C * t) (fun m => (hF6 m).restrict) (integrable_const _)
    (fun m => ae_restrict_of_ae (hbd m)) (ae_restrict_of_ae hlim)
  have e : (fun m => ∫ ω in A, G m ω ∂Q) = fun _ => 0 := funext fun m => hF2 m A hA
  rw [e] at hT
  exact (tendsto_nhds_unique tendsto_const_nhds hT).symm

end BlockBand.Diffusion
