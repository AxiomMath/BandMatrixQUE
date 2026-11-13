module
public import BlockBand.Diffusion.Duality.Calculus
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The windowed duality identity

**Main result (`window_identity`).** For a time window `χ` (`IsTimeWindow χ c c₂`,
`s < c < c₂ < t`: `χ = 0` before `c`, `χ = 1` after `c₂`), with
`F_χ(ω) = ∫_{(0,t]} χ'(r) u(r, Z_r(ω)) dr`, the function `u(t, Z_t) - F_χ` is a.e. strongly
measurable and `∫_A (u(t, Z_t) - F_χ) dQ = 0` for every `A ∈ 𝓖_s`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal

variable {d : ℕ}

/-!
### Deterministic part
-/

/-- The space-time domain `(-∞, c) × U ∪ (s, t) × O` in `ℝ^{d+1}` coordinates. -/
def windowDomain (U O : Set (Fin d → ℝ)) (c s t : ℝ) : Set (Fin (d + 1) → ℝ) :=
  stEquiv d ⁻¹' (Iio c ×ˢ U ∪ Ioo s t ×ˢ O)

/-- The cut test function `χ(y₀) u(y₀, tail y)`. -/
def cutFun (χ : ℝ → ℝ) (u : ℝ × (Fin d → ℝ) → ℝ) : (Fin (d + 1) → ℝ) → ℝ :=
  (fun q => χ q.1 * u q) ∘ stEquiv d

/-- Its generator `χ'(y₀) u(y₀, tail y)`. -/
def cutGen (χ : ℝ → ℝ) (u : ℝ × (Fin d → ℝ) → ℝ) (y : Fin (d + 1) → ℝ) : ℝ :=
  deriv χ (y 0) * u (stEquiv d y)

variable {U O : Set (Fin d → ℝ)} {c c₂ s t : ℝ} {χ : ℝ → ℝ} {u : ℝ × (Fin d → ℝ) → ℝ}

theorem isOpen_windowDomain (hU : IsOpen U) (hO : IsOpen O) :
    IsOpen (windowDomain U O c s t) :=
  (stEquiv d).continuous.isOpen_preimage _ ((isOpen_Iio.prod hU).union (isOpen_Ioo.prod hO))

theorem tail_mem_of_windowDomain (hOU : O ⊆ U) {y : Fin (d + 1) → ℝ}
    (hy : y ∈ windowDomain U O c s t) : Fin.tail y ∈ U := by
  rcases hy with h | h
  · exact h.2
  · exact hOU h.2

theorem mem_windowDomain_iff {y : Fin (d + 1) → ℝ} :
    y ∈ windowDomain U O c s t ↔ (y 0 < c ∧ Fin.tail y ∈ U) ∨
      (y 0 ∈ Ioo s t ∧ Fin.tail y ∈ O) := Iff.rfl

theorem cutFun_apply (y : Fin (d + 1) → ℝ) :
    cutFun χ u y = χ (y 0) * u (stEquiv d y) := rfl

theorem cutFun_eq_zero (hχ : IsTimeWindow χ c c₂) {y : Fin (d + 1) → ℝ} (hy : y 0 ≤ c) :
    cutFun χ u y = 0 := by
  rw [cutFun_apply, hχ.zero _ hy, zero_mul]

theorem contDiffOn_cutFun (hχ : IsTimeWindow χ c c₂) (hO : IsOpen O)
    (hu : ContDiffOn ℝ 2 u (Ioo s t ×ˢ O)) :
    ContDiffOn ℝ 2 (cutFun χ u) (windowDomain U O c s t) := by
  have hψ : ContDiffOn ℝ 2 (fun q : ℝ × (Fin d → ℝ) => χ q.1 * u q)
      (Iio c ×ˢ U ∪ Ioo s t ×ˢ O) := by
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    by_cases hx2 : x ∈ Ioo s t ×ˢ O
    · refine ⟨Ioo s t ×ˢ O, isOpen_Ioo.prod hO, hx2, ?_⟩
      exact (((hχ.contDiff.comp contDiff_fst).contDiffOn).mul hu).mono inter_subset_right
    · have hx1 : x ∈ Iio c ×ˢ (univ : Set (Fin d → ℝ)) := by
        rcases hx with h | h
        · exact ⟨h.1, mem_univ _⟩
        · exact absurd h hx2
      refine ⟨Iio c ×ˢ univ, isOpen_Iio.prod isOpen_univ, hx1, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr fun q hq => ?_
      rw [hχ.zero q.1 (le_of_lt hq.2.1), zero_mul]
  exact hψ.comp_continuousLinearMap (stEquiv d : (Fin (d + 1) → ℝ) →L[ℝ] ℝ × (Fin d → ℝ))

/-- Before the window the generator of the cut function vanishes. -/
theorem mpGenerator_cutFun_of_lt (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (hχ : IsTimeWindow χ c c₂)
    {y : Fin (d + 1) → ℝ} (hy : y 0 < c) :
    mpGenerator (stDrift b) (stCov a) (cutFun χ u) y = 0 := by
  rw [cutFun, mpGenerator_stDrift_comp]
  have hev : (fun q : ℝ × (Fin d → ℝ) => χ q.1 * u q) =ᶠ[𝓝 (stEquiv d y)] fun _ => 0 := by
    filter_upwards [prod_mem_nhds (Iio_mem_nhds hy) univ_mem] with q hq
    rw [hχ.zero q.1 (le_of_lt hq.1), zero_mul]
  rw [stGen_congr hev, stGen_zero]

/-- On the window domain the generator of the cut function is `χ' u`. -/
theorem mpGenerator_cutFun (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (hχ : IsTimeWindow χ c c₂) (hO : IsOpen O)
    (hu : ContDiffOn ℝ 2 u (Ioo s t ×ˢ O)) (hpde : ∀ p ∈ Ioo s t ×ˢ O, stGen b a u p = 0)
    {y : Fin (d + 1) → ℝ} (hy : y ∈ windowDomain U O c s t) :
    mpGenerator (stDrift b) (stCov a) (cutFun χ u) y = cutGen χ u y := by
  by_cases h2 : stEquiv d y ∈ Ioo s t ×ˢ O
  · rw [cutFun, mpGenerator_stDrift_comp, stGen_mul_time b a hχ.contDiff
      (hu.contDiffAt ((isOpen_Ioo.prod hO).mem_nhds h2)), hpde _ h2, mul_zero, add_zero]
    rfl
  · have h1 : y 0 < c := by
      rcases hy with h | h
      · exact h.1
      · exact absurd h h2
    rw [mpGenerator_cutFun_of_lt b a hχ h1, cutGen, hχ.deriv_eq_zero_of_lt h1, zero_mul]

theorem abs_cutFun_le (hχ : IsTimeWindow χ c c₂) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p ∈ Ioo s t ×ˢ O, |u p| ≤ C) {y : Fin (d + 1) → ℝ}
    (hy : y ∈ windowDomain U O c s t) : |cutFun χ u y| ≤ C := by
  by_cases h2 : stEquiv d y ∈ Ioo s t ×ˢ O
  · rw [cutFun_apply, abs_mul, abs_of_nonneg (hχ.nonneg _)]
    calc χ (y 0) * |u (stEquiv d y)| ≤ 1 * C :=
          mul_le_mul (hχ.le_one _) (hC _ h2) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · have h1 : y 0 < c := by
      rcases hy with h | h
      · exact h.1
      · exact absurd h h2
    rw [cutFun_eq_zero hχ h1.le, abs_zero]; exact hC0

theorem abs_cutGen_le (hχ : IsTimeWindow χ c c₂) {C K : ℝ} (hK : ∀ r, |deriv χ r| ≤ K)
    (hC0 : 0 ≤ C) (hC : ∀ p ∈ Ioo s t ×ˢ O, |u p| ≤ C) {y : Fin (d + 1) → ℝ}
    (hy : y ∈ windowDomain U O c s t) : |cutGen χ u y| ≤ K * C := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  by_cases h2 : stEquiv d y ∈ Ioo s t ×ˢ O
  · rw [cutGen, abs_mul]
    exact mul_le_mul (hK _) (hC _ h2) (abs_nonneg _) hK0
  · have h1 : y 0 < c := by
      rcases hy with h | h
      · exact h.1
      · exact absurd h h2
    rw [cutGen, hχ.deriv_eq_zero_of_lt h1, zero_mul, abs_zero]; exact mul_nonneg hK0 hC0

/-!
### Paths leaving the window domain at time `t`
-/

section Path

variable {Ω : Type*}

/-- If a continuous path stays in the open `V` before `t` and is outside `V` at `t`, then the
exit times from the exhaustion of `V` are `≤ t`, eventually `≥ t'` for each `t' < t`, and
eventually the path starts in the exhaustion set. -/
theorem exit_exhaust_facts {V : Set (Fin (d + 1) → ℝ)} (hV : IsOpen V)
    {Y : ℝ≥0 → Ω → Fin (d + 1) → ℝ} {ω : Ω} (hY : Continuous fun r => Y r ω) {T : ℝ≥0}
    (hin : ∀ r < T, Y r ω ∈ V) (hout : Y T ω ∉ V) :
    (∀ m, exitTimeFrom (exhaust V m) Y ω ≤ T) ∧
      (∀ t' < T, ∀ᶠ m in atTop, (t' : WithTop ℝ≥0) ≤ exitTimeFrom (exhaust V m) Y ω) := by
  refine ⟨fun m => iInf₂_le T fun h => hout (subset_closure.trans
    (closure_exhaust_subset_U m) h), fun t' ht' => ?_⟩
  have hK : IsCompact ((fun r => Y r ω) '' Icc 0 t') := isCompact_Icc.image hY
  obtain ⟨m₀, hm₀⟩ := exists_exhaust_of_compact hV hK (by
    rintro _ ⟨r, hr, rfl⟩; exact hin r (lt_of_le_of_lt hr.2 ht'))
  filter_upwards [eventually_ge_atTop m₀] with m hm
  refine le_iInf₂ fun r hr => ?_
  by_contra hlt
  push Not at hlt
  exact hr (exhaust_mono hm (hm₀ ⟨r, ⟨zero_le, (WithTop.coe_lt_coe.1 hlt).le⟩, rfl⟩))

theorem tendsto_stopTime_of_facts {τ : ℕ → WithTop ℝ≥0} {T : ℝ≥0} (h1 : ∀ m, τ m ≤ T)
    (h2 : ∀ t' < T, ∀ᶠ m in atTop, (t' : WithTop ℝ≥0) ≤ τ m) :
    Tendsto (fun m => stopTime (τ m) T) atTop (𝓝 T) := by
  have hst : ∀ m, (stopTime (τ m) T : WithTop ℝ≥0) = τ m := fun m => by
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ≥0, τ m = σ := WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top WithTop.coe_ne_top (h1 m)) |>.imp fun _ h => h.symm
    rw [hσ, stopTime_coe, min_eq_right (WithTop.coe_le_coe.1 (hσ ▸ h1 m))]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun m =>
    lt_of_le_of_lt (stopTime_le _ _) ha⟩
  obtain ⟨t', hat', ht'⟩ := exists_between ha
  filter_upwards [h2 t' ht'] with m hm
  rw [← hst m] at hm
  exact lt_of_lt_of_le hat' (WithTop.coe_le_coe.1 hm)

end Path

/-!
### The windowed identity
-/

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {Z : ℝ≥0 → Ω → Fin d → ℝ}

/-- `F_χ(ω) = ∫_{(0,t]} χ'(r) u(r, Z_r) dr`. -/
def windowAvg (χ : ℝ → ℝ) (u : ℝ × (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  ∫ r in Ioc (0 : ℝ) t, deriv χ r * u (r, Z r.toNNReal ω)

/-- **The windowed duality identity**: `∫_A (u(t, Z_t) - F_χ) dQ = 0` for `A ∈ 𝓖_s`. -/
theorem window_identity (hZ : IsMPSolutionOn Q 𝓖 b a U Z) (hU : IsOpen U) (hO : IsOpen O)
    (hOU : O ⊆ U) (hb : ContinuousOn b U) (ha : ContinuousOn a U) {s t : ℝ≥0}
    (hsc : (s : ℝ) < c) (hct : c₂ < t) (hχ : IsTimeWindow χ c c₂)
    (hu2 : ContDiffOn ℝ 2 u (Ioo (s : ℝ) t ×ˢ O))
    (hpde : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, stGen b a u p = 0)
    (huc : ∀ x ∈ O, ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((t : ℝ), x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ C)
    (hpath : ∀ᵐ ω ∂Q, (∀ r ≤ t, Z r ω ∈ U) ∧ ∀ r, s < r → r ≤ t → Z r ω ∈ O) :
    AEStronglyMeasurable (fun ω => u ((t : ℝ), Z t ω) - windowAvg χ u Z t ω) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, (u ((t : ℝ), Z t ω) - windowAvg χ u Z t ω) ∂Q = 0 := by
  have hcc : c ≤ c₂ := by
    by_contra hlt
    push Not at hlt
    have := hχ.zero c₂ hlt.le
    rw [hχ.one c₂ le_rfl] at this
    exact one_ne_zero this
  have hst : s ≤ t := by
    have : (s : ℝ) < t := by linarith
    exact_mod_cast this.le
  have hCo : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, |u p| ≤ C := fun p hp =>
    hC p ⟨Ioo_subset_Ioc_self hp.1, hp.2⟩
  set V := windowDomain U O c s t with hVdef
  have hV : IsOpen V := isOpen_windowDomain hU hO
  have hVU : ∀ y ∈ V, Fin.tail y ∈ U := fun y hy => tail_mem_of_windowDomain hOU hy
  have hY := IsMPSolutionOn.spaceTime hZ hU hb ha hVU
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
  have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Z r ω) ∧ (∀ r ≤ t, Z r ω ∈ U) ∧
      ∀ r, s < r → r ≤ t → Z r ω ∈ O := by
    filter_upwards [hZ.continuous, hpath] with ω h1 h2 using ⟨h1, h2⟩
  -- pathwise facts
  have hpw : ∀ ω, Continuous (fun r => Z r ω) → (∀ r ≤ t, Z r ω ∈ U) →
      (∀ r, s < r → r ≤ t → Z r ω ∈ O) →
      Tendsto (fun m => G m ω) atTop (𝓝 (H ω)) ∧ ∀ m, |G m ω| ≤ C + K * C * t := by
    intro ω hZc hZU hZO
    have hYc : Continuous fun r => Y r ω := continuous_stProc hZc
    have hin : ∀ r < t, Y r ω ∈ V := fun r hr => by
      by_cases hrc : (r : ℝ) < c
      · exact Or.inl ⟨hrc, by simpa [hYdef] using hZU r hr.le⟩
      · push Not at hrc
        have hsr : s < r := by exact_mod_cast lt_of_lt_of_le hsc hrc
        refine Or.inr ⟨⟨by simpa [hYdef] using lt_of_lt_of_le hsc hrc,
          by simpa [hYdef] using hr⟩, by simpa [hYdef] using hZO r hsr hr.le⟩
    have hout : Y t ω ∉ V := by
      rintro (h | h)
      · have : (t : ℝ) < c := by simpa [hYdef] using h.1
        linarith
      · have : (t : ℝ) < t := by simpa [hYdef] using h.1.2
        exact lt_irrefl _ this
    have hY0 : Y 0 ω ∈ V := hin 0 (lt_of_le_of_lt zero_le (by exact_mod_cast
      (lt_of_le_of_lt (NNReal.coe_nonneg s) (lt_of_lt_of_le hsc (hcc.trans hct.le)))))
    obtain ⟨hτ1, hτ2⟩ := exit_exhaust_facts hV hYc hin hout
    have hσlim : Tendsto (fun m => stopTime (τ m ω) t) atTop (𝓝 t) :=
      tendsto_stopTime_of_facts hτ1 hτ2
    have hσlimR : Tendsto (fun m => (stopTime (τ m ω) t : ℝ)) atTop (𝓝 (t : ℝ)) :=
      (NNReal.continuous_coe.tendsto t).comp hσlim
    have hst' : s < t := by
      have : (s : ℝ) < t := by linarith
      exact_mod_cast this
    have hev1 : ∀ᶠ m in atTop, c₂ < (stopTime (τ m ω) t : ℝ) := hσlimR.eventually_const_lt hct
    have hclos : ∀ m, ∀ r ∈ Ioc (0 : ℝ) (stopTime (τ m ω) t), Y r.toNNReal ω ∈ V :=
      fun m r hr =>
        closure_exhaust_subset_U m ((stopped_path_mem_closure (isOpen_exhaust m) hYc t).1 r hr)
    have hend : ∀ m, Y (stopTime (τ m ω) t) ω ∈ V := fun m => by
      rcases (stopped_path_mem_closure (isOpen_exhaust m) hYc t).2 with h | ⟨h, -⟩
      · rw [h]; exact hY0
      · exact closure_exhaust_subset_U m h
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
    refine ⟨?_, fun m => ?_⟩
    · have hZt : Z t ω ∈ O := hZO t hst' le_rfl
      have hp : Tendsto (fun m => ((stopTime (τ m ω) t : ℝ), Z (stopTime (τ m ω) t) ω)) atTop
          (𝓝[Ioc (s : ℝ) t ×ˢ O] ((t : ℝ), Z t ω)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hσlimR.prodMk_nhds ((hZc.tendsto t).comp hσlim), ?_⟩
        filter_upwards [hev1] with m hm
        have hsσ : (s : ℝ) < stopTime (τ m ω) t := by linarith
        refine ⟨⟨hsσ, NNReal.coe_le_coe.2 (stopTime_le _ _)⟩, hZO _ ?_ (stopTime_le _ _)⟩
        exact_mod_cast hsσ
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
    · rw [hGe m]
      have h1 := abs_cutFun_le hχ hC0 hCo (hend m)
      have h2 : |∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t), L (Y r'.toNNReal ω)| ≤ K * C * t :=
        abs_integral_stop_le (isOpen_exhaust m) hYc (g := L) (mul_nonneg hK0 hC0)
          (fun y hy => by
            rw [hLdef, mpGenerator_cutFun b a hχ hO hu2 hpde (closure_exhaust_subset_U m hy)]
            exact abs_cutGen_le hχ hK hC0 hCo (closure_exhaust_subset_U m hy)) le_rfl
      rw [hint m] at h2
      calc _ ≤ |φ (Y (stopTime (τ m ω) t) ω)| + |∫ r' in Ioc (0 : ℝ) (stopTime (τ m ω) t),
            deriv χ r' * u (r', Z r'.toNNReal ω)| := abs_sub _ _
        _ ≤ C + K * C * t := add_le_add h1 h2
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
