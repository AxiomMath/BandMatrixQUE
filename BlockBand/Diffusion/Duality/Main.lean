module
public import BlockBand.Diffusion.Duality.Core
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Space-time duality for martingale-problem solutions

Setting: `(Ω, 𝓖, Q)` a probability space with a **raw** filtration (no completion, no right
continuity); `U ⊆ ℝ^d` open, `b, a` continuous on `U`, `a` symmetric on `U`; `Z` a solution
of the raw test-function martingale problem `IsTestMPSolution Q 𝓖 b a U Z`
(`f(Z_t) - ∫_0^t 𝓛f(Z_r) dr` a `𝓖`-martingale for every `C_c^∞` test `f` supported in `U`,
paths a.s. continuous), `Z_0 = z ∈ U` a.s.; `O ⊆ U` open; `t > 0`; a.s. `Z_r ∈ O` for all
`r ∈ (0, t]` (the start `z` may lie on `∂O`).

`u : ℝ × ℝ^d → ℝ` is jointly `C²` on `(0, t) × O` with `∂_s u + 𝓛 u = 0` there (`stGen`),
continuous on `(0, t] × O`, continuous within `(0, t] × O` at `(0, z)`, and bounded on
`(0, t] × O`. No regularity of `u` up to `∂O`, and no `C²` in time up to `s = 0` or `s = t`,
is assumed.

## Main results

* `IsTestMPSolution.duality`: `E[u(t, Z_t)] = u(0, z)`.
* `IsTestMPSolution.duality_setIntegral`: for `s < t` and `A ∈ 𝓖_s`,
  `∫_A u(t, Z_t) dQ = ∫_A u(s, Z_s) dQ`.
* `IsTestMPSolution.condExp_duality`: for `s < t`, `E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s.

With `f := u(t, ·)` on `O` these read `E[f(Z_t)] = u(0, z)` and `E[f(Z_t) | 𝓖_s] = u(s, Z_s)`.

Proof. `window_identity` gives
`∫_A u(t, Z_t) = ∫_A ∫_{(0,t]} χ_k'(r) u(r, Z_r) dr` for smooth time windows `χ_k` rising on
`[c_k, c₂_k] ⊆ (s, t)`; letting `c₂_k ↓ s`, the window averages tend pathwise to `u(s, Z_s)`
(right continuity of `r ↦ u(r, Z_r)` at `s`, `χ_k' ≥ 0`, `∫ χ_k' = 1`) and are bounded by
`sup |u|`; dominated convergence.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {d : ℕ}

/-!
### Window averages
-/

theorem IsTimeWindow.le {χ : ℝ → ℝ} {c c₂ : ℝ} (h : IsTimeWindow χ c c₂) : c ≤ c₂ := by
  by_contra hlt
  push Not at hlt
  have := h.zero c₂ hlt.le
  rw [h.one c₂ le_rfl] at this
  exact one_ne_zero this

theorem integrableOn_window {χ : ℝ → ℝ} {c c₂ s t : ℝ} (hχ : IsTimeWindow χ c c₂) (hsc : s < c)
    (hct : c₂ ≤ t) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioc s t)) :
    IntegrableOn (fun r => deriv χ r * f r) (Ioc 0 t) := by
  have hsub : Icc c c₂ ⊆ Ioc s t := fun r hr => ⟨lt_of_lt_of_le hsc hr.1, hr.2.trans hct⟩
  have h1 : IntegrableOn (fun r => deriv χ r * f r) (Icc c c₂) :=
    ((hχ.continuous_deriv.continuousOn).mul (hf.mono hsub)).integrableOn_Icc
  exact h1.of_forall_sdiff_eq_zero measurableSet_Ioc fun r hr => by
    rw [hχ.deriv_eq_zero hr.2, zero_mul]

/-- A window average of a function bounded by `C` on `(s, t]` is bounded by `C`. -/
theorem abs_windowIntegral_le {χ : ℝ → ℝ} {c c₂ s t : ℝ} (hχ : IsTimeWindow χ c c₂)
    (hs0 : 0 ≤ s) (hsc : s < c) (hct : c₂ ≤ t) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ r ∈ Ioc s t, |f r| ≤ C) :
    |∫ r in Ioc (0 : ℝ) t, deriv χ r * f r| ≤ C := by
  have hg : IntegrableOn (fun r => deriv χ r * C) (Ioc 0 t) :=
    (hχ.continuous_deriv.mul continuous_const).integrableOn_Ioc
  have h := norm_integral_le_of_norm_le (f := fun r => deriv χ r * f r) hg
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ.deriv_nonneg r)]
      by_cases hr' : r ∈ Icc c c₂
      · exact mul_le_mul_of_nonneg_left (hf r ⟨lt_of_lt_of_le hsc hr'.1, hr'.2.trans hct⟩)
          (hχ.deriv_nonneg r)
      · rw [hχ.deriv_eq_zero hr', zero_mul, zero_mul]))
  rw [Real.norm_eq_abs, integral_mul_const, hχ.integral_deriv (hs0.trans hsc.le) hct,
    one_mul] at h
  exact h

/-- **Window averages converge** to the right limit at `s`. -/
theorem tendsto_windowIntegral {f : ℝ → ℝ} {s t L : ℝ} (hs0 : 0 ≤ s)
    (hf : ContinuousOn f (Ioc s t)) (hfL : Tendsto f (𝓝[>] s) (𝓝 L))
    {cs c₂s : ℕ → ℝ} {χs : ℕ → ℝ → ℝ} (hχ : ∀ k, IsTimeWindow (χs k) (cs k) (c₂s k))
    (hsc : ∀ k, s < cs k) (hct : ∀ k, c₂s k < t) (hlim : Tendsto c₂s atTop (𝓝 s)) :
    Tendsto (fun k => ∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * f r) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ r in 𝓝[>] s, f r ∈ Metric.ball L (ε / 2) :=
    hfL.eventually (Metric.ball_mem_nhds L (half_pos hε))
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hu'))
  refine ⟨N, fun k hk => ?_⟩
  have hk' : c₂s k < u' := hN k hk
  have hint := integrableOn_window (hχ k) (hsc k) (hct k).le hf
  have hone := (hχ k).integral_deriv (hs0.trans (hsc k).le) (hct k).le
  have hcL : IntegrableOn (fun r => deriv (χs k) r * L) (Ioc 0 t) :=
    ((hχ k).continuous_deriv.mul continuous_const).integrableOn_Ioc
  have e : (∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * f r) - L =
      ∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * (f r - L) := by
    have h1 : ∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * (f r - L) =
        (∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * f r) -
          ∫ r in Ioc (0 : ℝ) t, deriv (χs k) r * L := by
      rw [← integral_sub hint hcL]; congr 1; funext r; ring
    rw [h1, integral_mul_const, hone, one_mul]
  have hg : IntegrableOn (fun r => deriv (χs k) r * (ε / 2)) (Ioc 0 t) :=
    ((hχ k).continuous_deriv.mul continuous_const).integrableOn_Ioc
  have h := norm_integral_le_of_norm_le (f := fun r => deriv (χs k) r * (f r - L)) hg
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hχ k).deriv_nonneg r)]
      by_cases hr' : r ∈ Icc (cs k) (c₂s k)
      · refine mul_le_mul_of_nonneg_left ?_ ((hχ k).deriv_nonneg r)
        have := hsub ⟨lt_of_lt_of_le (hsc k) hr'.1, lt_of_le_of_lt hr'.2 hk'⟩
        rw [← Real.dist_eq]; exact (Metric.mem_ball.1 this).le
      · rw [(hχ k).deriv_eq_zero hr', zero_mul, zero_mul]))
  rw [integral_mul_const, hone, one_mul, ← e, Real.norm_eq_abs] at h
  rw [Real.dist_eq]
  linarith

/-!
### Measurability of `g(X)` for `g` continuous on an open set containing `X` a.s.
-/

theorem aestronglyMeasurable_comp_continuousOn {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {m : MeasurableSpace Ω} {X : Ω → Fin d → ℝ} (hX : Measurable[m] X) {g : (Fin d → ℝ) → ℝ}
    {O : Set (Fin d → ℝ)} (hO : IsOpen O) (hg : ContinuousOn g O) (hXO : ∀ᵐ ω ∂Q, X ω ∈ O) :
    AEStronglyMeasurable[m] (fun ω => g (X ω)) Q := by
  classical
  have hm : Measurable (O.piecewise g 0) :=
    hg.measurable_piecewise continuousOn_const hO.measurableSet
  refine ⟨fun ω => O.piecewise g 0 (X ω), (hm.comp hX).stronglyMeasurable, ?_⟩
  filter_upwards [hXO] with ω hω
  simp [Set.piecewise, hω]

/-!
### The duality identity for `IsMPSolutionOn`
-/

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U O : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ} {u : ℝ × (Fin d → ℝ) → ℝ}

/-- Duality from time `s` to `t` for the localized martingale problem `IsMPSolutionOn`. -/
theorem duality_setIntegral_mp (hZ : IsMPSolutionOn Q 𝓖 b a U Z) (hU : IsOpen U)
    (hO : IsOpen O) (hOU : O ⊆ U) (hb : ContinuousOn b U) (ha : ContinuousOn a U)
    {s t : ℝ≥0} (hst : s < t) (hu2 : ContDiffOn ℝ 2 u (Ioo (s : ℝ) t ×ˢ O))
    (hpde : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, stGen b a u p = 0)
    (hcont : ContinuousOn u (Ioc (s : ℝ) t ×ˢ O))
    (hcs : ∀ᵐ ω ∂Q, ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((s : ℝ), Z s ω))
    {C : ℝ} (hC : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ C)
    (hpath : ∀ᵐ ω ∂Q, (∀ r ≤ t, Z r ω ∈ U) ∧ ∀ r, s < r → r ≤ t → Z r ω ∈ O) :
    Integrable (fun ω => u ((t : ℝ), Z t ω)) Q ∧ Integrable (fun ω => u ((s : ℝ), Z s ω)) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q := by
  set C' := max C 0 with hC'def
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC' : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ C' := fun p hp => (hC p hp).trans
    (le_max_left _ _)
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
  set δ : ℝ := (t : ℝ) - s with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set cs : ℕ → ℝ := fun k => s + δ / ((k : ℝ) + 3) with hcs_def
  set c₂s : ℕ → ℝ := fun k => s + 2 * δ / ((k : ℝ) + 3) with hc₂s_def
  have hk3 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 3 := fun k => by positivity
  have h1 : ∀ k, (s : ℝ) < cs k := fun k => by
    simp only [hcs_def]; have := div_pos hδ0 (hk3 k); linarith
  have h2 : ∀ k, cs k < c₂s k := fun k => by
    simp only [hcs_def, hc₂s_def]
    have : δ / ((k : ℝ) + 3) < 2 * δ / ((k : ℝ) + 3) :=
      div_lt_div_of_pos_right (by linarith) (hk3 k)
    linarith
  have h3 : ∀ k, c₂s k < t := fun k => by
    simp only [hc₂s_def]
    have : 2 * δ / ((k : ℝ) + 3) < δ := by
      rw [div_lt_iff₀ (hk3 k)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    linarith
  have hlim : Tendsto c₂s atTop (𝓝 s) := by
    have : Tendsto (fun k : ℕ => 2 * δ / ((k : ℝ) + 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [hc₂s_def] using (tendsto_const_nhds (x := (s : ℝ))).add this
  set χs : ℕ → ℝ → ℝ := fun k r => Real.smoothTransition ((r - cs k) / (c₂s k - cs k))
  have hχ : ∀ k, IsTimeWindow (χs k) (cs k) (c₂s k) := fun k =>
    isTimeWindow_smoothTransition (h2 k)
  have hW : ∀ k, _ := fun k => window_identity hZ hU hO hOU hb ha (h1 k) (h3 k) (hχ k) hu2 hpde
    (fun x hx => hcont _ ⟨⟨hstR, le_rfl⟩, hx⟩) hC0 hC' hpath
  -- the terminal value
  have hZt : ∀ᵐ ω ∂Q, Z t ω ∈ O := hpath.mono fun ω h => h.2 t hst le_rfl
  have hψm : AEStronglyMeasurable (fun ω => u ((t : ℝ), Z t ω)) Q :=
    aestronglyMeasurable_comp_continuousOn (((hZ.adapted t).measurable).mono (𝓖.le t) le_rfl)
      hO (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun x hx => ⟨⟨hstR, le_rfl⟩, hx⟩) hZt
  have hψi : Integrable (fun ω => u ((t : ℝ), Z t ω)) Q :=
    Integrable.of_bound hψm C' (hZt.mono fun ω hω => by
      rw [Real.norm_eq_abs]; exact hC' _ ⟨⟨hstR, le_rfl⟩, hω⟩)
  -- the window averages
  set F : ℕ → Ω → ℝ := fun k => windowAvg (χs k) u Z t with hFdef
  have hFm : ∀ k, AEStronglyMeasurable (F k) Q := fun k =>
    (hψm.sub (hW k).1).congr (ae_of_all _ fun ω => by simp [hFdef])
  have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Z r ω) ∧ (∀ r, s < r → r ≤ t → Z r ω ∈ O) ∧
      ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((s : ℝ), Z s ω) := by
    filter_upwards [hZ.continuous, hpath, hcs] with ω h1 h2 h3 using ⟨h1, h2.2, h3⟩
  have hmem : ∀ ω, (∀ r, s < r → r ≤ t → Z r ω ∈ O) → ∀ r ∈ Ioc (s : ℝ) t,
      (r, Z r.toNNReal ω) ∈ Ioc (s : ℝ) t ×ˢ O := fun ω hO' r hr => by
    refine ⟨hr, hO' _ ?_ ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hs0.trans hr.1.le)]; exact hr.1
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hs0.trans hr.1.le)]; exact hr.2
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖F k ω‖ ≤ C' := fun k => hgood.mono fun ω h => by
    rw [Real.norm_eq_abs]
    exact abs_windowIntegral_le (hχ k) hs0 (h1 k) (h3 k).le fun r hr => hC' _ (hmem ω h.2.1 r hr)
  have hlimF : ∀ᵐ ω ∂Q, Tendsto (fun k => F k ω) atTop (𝓝 (u ((s : ℝ), Z s ω))) :=
    hgood.mono fun ω h => by
      have hpc : Continuous fun r : ℝ => (r, Z r.toNNReal ω) :=
        continuous_id.prodMk (h.1.comp continuous_real_toNNReal)
      refine tendsto_windowIntegral hs0 (hcont.comp hpc.continuousOn (hmem ω h.2.1)) ?_ hχ h1 h3
        hlim
      have hp : Tendsto (fun r : ℝ => (r, Z r.toNNReal ω)) (𝓝[>] (s : ℝ))
          (𝓝[Ioc (s : ℝ) t ×ˢ O] ((s : ℝ), Z s ω)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := (hpc.tendsto (s : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (s : ℝ)))
          simpa only [Real.toNNReal_coe] using this
        · filter_upwards [Ioo_mem_nhdsGT hstR] with r hr
          exact hmem ω h.2.1 r ⟨hr.1, hr.2.le⟩
      exact h.2.2.tendsto.comp hp
  have hLm : AEStronglyMeasurable (fun ω => u ((s : ℝ), Z s ω)) Q :=
    aestronglyMeasurable_of_tendsto_ae atTop hFm hlimF
  have hLb : ∀ᵐ ω ∂Q, ‖u ((s : ℝ), Z s ω)‖ ≤ C' := by
    filter_upwards [hlimF, ae_all_iff.2 hbd] with ω hl hb'
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp hl) hb'
  have hLi : Integrable (fun ω => u ((s : ℝ), Z s ω)) Q := Integrable.of_bound hLm C' hLb
  refine ⟨hψi, hLi, fun A hA => ?_⟩
  have hFi : ∀ k, Integrable (F k) Q := fun k => Integrable.of_bound (hFm k) C' (hbd k)
  have heq : ∀ k, ∫ ω in A, F k ω ∂Q = ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q := fun k => by
    have := (hW k).2 A hA
    rw [integral_sub hψi.integrableOn (hFi k).integrableOn, sub_eq_zero] at this
    exact this.symm
  have hT := tendsto_integral_of_dominated_convergence (μ := Q.restrict A) (fun _ => C')
    (fun k => (hFm k).restrict) (integrable_const _) (fun k => ae_restrict_of_ae (hbd k))
    (ae_restrict_of_ae hlimF)
  have e : (fun k => ∫ ω in A, F k ω ∂Q) = fun _ => ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q :=
    funext heq
  rw [e] at hT
  exact tendsto_nhds_unique tendsto_const_nhds hT

/-!
### Main results for the raw test-function martingale problem
-/

section Headline

variable (hZ : IsTestMPSolution Q 𝓖 b a U Z) (hU : IsOpen U) (hb : ContinuousOn b U)
  (ha : ContinuousOn a U) (hsym : ∀ y ∈ U, ∀ i j, a y i j = a y j i) (hO : IsOpen O)
  (hOU : O ⊆ U) {z : Fin d → ℝ} (hzU : z ∈ U) (hz : ∀ᵐ ω ∂Q, Z 0 ω = z) {t : ℝ≥0}
  (hin : ∀ᵐ ω ∂Q, ∀ r, 0 < r → r ≤ t → Z r ω ∈ O)
  (hu2 : ContDiffOn ℝ 2 u (Ioo 0 (t : ℝ) ×ˢ O))
  (hpde : ∀ p ∈ Ioo 0 (t : ℝ) ×ˢ O, stGen b a u p = 0)
  (hcont : ContinuousOn u (Ioc 0 (t : ℝ) ×ˢ O))
  (hu0 : ContinuousWithinAt u (Ioc 0 (t : ℝ) ×ˢ O) (0, z))
  {C : ℝ} (hC : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ O, |u p| ≤ C)
include hZ hU hb ha hsym hO hOU hzU hz hin hu2 hpde hcont hu0 hC

theorem IsTestMPSolution.duality_aux {s : ℝ≥0} (hst : s < t) :
    Integrable (fun ω => u ((t : ℝ), Z t ω)) Q ∧ Integrable (fun ω => u ((s : ℝ), Z s ω)) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q := by
  have hZ' := hZ.isMPSolutionOn hU hb ha hsym
  have hsub : Ioc (s : ℝ) t ×ˢ O ⊆ Ioc 0 (t : ℝ) ×ˢ O :=
    prod_mono (Ioc_subset_Ioc_left (NNReal.coe_nonneg s)) le_rfl
  have hsub' : Ioo (s : ℝ) t ×ˢ O ⊆ Ioo 0 (t : ℝ) ×ˢ O :=
    prod_mono (Ioo_subset_Ioo_left (NNReal.coe_nonneg s)) le_rfl
  refine duality_setIntegral_mp hZ' hU hO hOU hb ha hst (hu2.mono hsub')
    (fun p hp => hpde p (hsub' hp)) (hcont.mono hsub) ?_ (fun p hp => hC p (hsub hp)) ?_
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · subst h0
      filter_upwards [hz] with ω hω
      simpa [hω] using hu0
    · filter_upwards [hin] with ω hω
      have hmem : ((s : ℝ), Z s ω) ∈ Ioc 0 (t : ℝ) ×ˢ O :=
        ⟨⟨by exact_mod_cast h0, by exact_mod_cast hst.le⟩, hω s h0 hst.le⟩
      exact (hcont _ hmem).mono hsub
  · filter_upwards [hz, hin] with ω h0 hω
    refine ⟨fun r hr => ?_, fun r hr hrt => hω r (lt_of_le_of_lt zero_le hr) hrt⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h | h
    · subst h; rw [h0]; exact hzU
    · exact hOU (hω r h hr)

/-- **Space-time duality, conditional form on sets.** For `s < t` and `A ∈ 𝓖_s`,
`∫_A u(t, Z_t) dQ = ∫_A u(s, Z_s) dQ`. -/
theorem IsTestMPSolution.duality_setIntegral {s : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q :=
  (hZ.duality_aux hU hb ha hsym hO hOU hzU hz hin hu2 hpde hcont hu0 hC hst).2.2 A hA

/-- **Space-time duality.** `E[u(t, Z_t)] = u(0, z)`. -/
theorem IsTestMPSolution.duality (ht : 0 < t) : ∫ ω, u ((t : ℝ), Z t ω) ∂Q = u (0, z) := by
  have h := hZ.duality_setIntegral hU hb ha hsym hO hOU hzU hz hin hu2 hpde hcont hu0 hC ht
    (MeasurableSet.univ (m := 𝓖 0))
  simp only [Measure.restrict_univ] at h
  rw [h, integral_congr_ae (g := fun _ => u (0, z)) (hz.mono fun ω hω => by simp [hω])]
  simp

/-- **Space-time duality, conditional expectation form.** For `s < t`, `E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s. -/
theorem IsTestMPSolution.condExp_duality {s : ℝ≥0} (hst : s < t) :
    Q[fun ω => u ((t : ℝ), Z t ω) | 𝓖 s] =ᵐ[Q] fun ω => u ((s : ℝ), Z s ω) := by
  obtain ⟨hψi, hLi, hI⟩ := hZ.duality_aux hU hb ha hsym hO hOU hzU hz hin hu2 hpde hcont hu0 hC
    hst
  have hgm : AEStronglyMeasurable[𝓖 s] (fun ω => u ((s : ℝ), Z s ω)) Q := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · subst h0
      refine ⟨fun _ => u (0, z), stronglyMeasurable_const, ?_⟩
      filter_upwards [hz] with ω hω
      simp [hω]
    · have hmeas : Measurable[𝓖 s] (Z s) := hZ.adapted s
      refine aestronglyMeasurable_comp_continuousOn (g := fun x => u ((s : ℝ), x)) hmeas hO ?_
        (hin.mono fun ω hω =>
        hω s h0 hst.le)
      exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun x hx => ⟨⟨by exact_mod_cast h0, by exact_mod_cast hst.le⟩, hx⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) hψi (fun A _ _ => hLi.integrableOn)
    (fun A hA _ => (hI A hA).symm) hgm).symm

end Headline

end BlockBand.Diffusion
