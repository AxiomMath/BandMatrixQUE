module
public import BlockBand.Diffusion.Doob.KilledCore
public import BlockBand.Diffusion.Duality.MollifyDuality
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Space-time duality for a killed path

Setting of `dk_window_identity_killed`: a.s. `Z_r ∈ O` for `r < ζ` and `Z_r = κ ∉ O` for `r ≥ ζ`;
`u(r, κ) = 0` and `|u(r, x)| ≤ L |x - κ|` on `(s, t] × O`.

## Main results
* `dk_duality_setIntegral_killed` (`IsMPSolutionOn`, `u` jointly `C²` on `(s, t) × O`): for
  `A ∈ 𝓖_s`, `∫_A u(t, Z_t) dQ = ∫_A u(s, Z_s) dQ` (the killed version of
  `duality_setIntegral_mp`).
* `dk_duality_C02_killed` (`IsTestMPSolution`, `u` only `C^{0,2}` on `(0, t) × O`, `IsC02On`,
  with `∂ₜu + 𝓛u = 0` there): the same identity for `0 < s < t` (the killed
  version of `IsTestMPSolution.duality_aux_pos_C02`).

Proofs: those of the unkilled versions, with the killed window identity and the extra pathwise
case `ζ ≤ r`, where `u(r, Z_r) = 0` and `|u(r', Z_{r'})| ≤ |L| |Z_{r'} - κ| → 0`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {d : ℕ}

/-!
### Pathwise facts on a killed path
-/

section Pathwise

variable {O : Set (Fin d → ℝ)} {u : ℝ × (Fin d → ℝ) → ℝ} {κ : Fin d → ℝ} {Lc : ℝ}
  {Ω : Type*} {Z : ℝ≥0 → Ω → Fin d → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- On a killed path, `|u(r, Z_r)| ≤ |L| |Z_r - κ|` on `(a, b]`. -/
theorem dk_abs_le_dist (hu0 : ∀ r, u (r, κ) = 0) {a b : ℝ}
    (hlin : ∀ p ∈ Ioc a b ×ˢ O, |u p| ≤ Lc * ‖p.2 - κ‖)
    (hZO : ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) (hZκ : ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ)
    {r : ℝ} (hr : r ∈ Ioc a b) : |u (r, Z r.toNNReal ω)| ≤ |Lc| * ‖Z r.toNNReal ω - κ‖ := by
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω
  · exact (hlin _ ⟨hr, hZO _ h⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (norm_nonneg _))
  · push Not at h
    rw [hZκ _ h, hu0, abs_zero]; positivity

/-- On a killed path, `r ↦ u(r, Z_r)` is continuous on `(a, b]`. -/
theorem dk_continuousOn_killed {a b : ℝ} (hcont : ContinuousOn u (Ioc a b ×ˢ O))
    (hu0 : ∀ r, u (r, κ) = 0) (hlin : ∀ p ∈ Ioc a b ×ˢ O, |u p| ≤ Lc * ‖p.2 - κ‖)
    (hZc : Continuous fun r => Z r ω)
    (hZO : ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) (hZκ : ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ) :
    ContinuousOn (fun r : ℝ => u (r, Z r.toNNReal ω)) (Ioc a b) := by
  intro r₀ hr₀
  have hpc : Continuous fun r : ℝ => (r, Z r.toNNReal ω) :=
    continuous_id.prodMk (hZc.comp continuous_real_toNNReal)
  by_cases h : ((r₀.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω
  · set W : Set ℝ := {r | ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω} with hW
    have hWo : IsOpen W := isOpen_lt (ENNReal.continuous_coe.comp continuous_real_toNNReal)
      continuous_const
    have h1 : ContinuousWithinAt (fun r : ℝ => u (r, Z r.toNNReal ω)) (Ioc a b ∩ W) r₀ :=
      (hcont _ ⟨hr₀, hZO _ h⟩).comp hpc.continuousWithinAt fun r hr => ⟨hr.1, hZO _ hr.2⟩
    exact (continuousWithinAt_inter (hWo.mem_nhds h)).1 h1
  · push Not at h
    have hκ0 : Z r₀.toNNReal ω = κ := hZκ _ h
    show Tendsto (fun r : ℝ => u (r, Z r.toNNReal ω)) (𝓝[Ioc a b] r₀)
      (𝓝 (u (r₀, Z r₀.toNNReal ω)))
    rw [hκ0, hu0]
    have hn : Tendsto (fun r : ℝ => |Lc| * ‖Z r.toNNReal ω - κ‖) (𝓝[Ioc a b] r₀) (𝓝 0) := by
      have hc : Continuous fun r : ℝ => ‖Z r.toNNReal ω - κ‖ :=
        continuous_norm.comp ((hZc.comp continuous_real_toNNReal).sub continuous_const)
      have := (hc.tendsto r₀).const_mul |Lc|
      simpa [hκ0] using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hn
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Real.norm_eq_abs]
    exact dk_abs_le_dist hu0 hlin hZO hZκ hr

end Pathwise

/-!
### Measurability of `u(r, Z_r)` on a killed path
-/

theorem dk_aestronglyMeasurable_killed {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {m : MeasurableSpace Ω} {X : Ω → Fin d → ℝ} (hX : Measurable[m] X) {g : (Fin d → ℝ) → ℝ}
    {O : Set (Fin d → ℝ)} (hO : IsOpen O) (hg : ContinuousOn g O) {κ : Fin d → ℝ}
    (hgκ : g κ = 0) (hXO : ∀ᵐ ω ∂Q, X ω ∈ O ∨ X ω = κ) :
    AEStronglyMeasurable[m] (fun ω => g (X ω)) Q := by
  classical
  have hm : Measurable (O.piecewise g 0) :=
    hg.measurable_piecewise continuousOn_const hO.measurableSet
  refine ⟨fun ω => O.piecewise g 0 (X ω), (hm.comp hX).stronglyMeasurable, ?_⟩
  filter_upwards [hXO] with ω hω
  rcases hω with h | h
  · simp [Set.piecewise, h]
  · rw [h]
    by_cases hκO : κ ∈ O <;> simp [Set.piecewise, hκO, hgκ]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {O : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ} {u : ℝ × (Fin d → ℝ) → ℝ}

/-!
### Killed duality for `C²` functions
-/

/-- **Killed duality from time `s` to time `t`** for the localized martingale problem
`IsMPSolutionOn`. -/
theorem dk_duality_setIntegral_killed (hZ : IsMPSolutionOn Q 𝓖 b a O Z) (hO : IsOpen O)
    (hb : ContinuousOn b O) (ha : ContinuousOn a O) {s t : ℝ≥0} (hst : s < t)
    (hu2 : ContDiffOn ℝ 2 u (Ioo (s : ℝ) t ×ˢ O))
    (hpde : ∀ p ∈ Ioo (s : ℝ) t ×ˢ O, stGen b a u p = 0)
    (hcont : ContinuousOn u (Ioc (s : ℝ) t ×ˢ O))
    (hcs : ∀ᵐ ω ∂Q, Z s ω ∈ O → ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((s : ℝ), Z s ω))
    {κ : Fin d → ℝ} (hκ : κ ∉ O) (hu0 : ∀ r, u (r, κ) = 0) {Lc : ℝ}
    (hlin : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ Lc * ‖p.2 - κ‖)
    {C : ℝ} (hC : ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |u p| ≤ C) {ζ : Ω → ℝ≥0∞}
    (hpath : ∀ᵐ ω ∂Q, (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) ∧
      ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ) :
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
  have hW : ∀ k, _ := fun k => dk_window_identity_killed hZ hO hb ha (h1 k) (h3 k) (hχ k) hu2
    hpde (fun x hx => hcont _ ⟨⟨hstR, le_rfl⟩, hx⟩) hκ hu0 hlin hC0 hC' hpath
  -- the paths sit in `O ∪ {κ}`
  have hOκ : ∀ r : ℝ≥0, ∀ᵐ ω ∂Q, Z r ω ∈ O ∨ Z r ω = κ := fun r => hpath.mono fun ω h => by
    by_cases hr : (r : ℝ≥0∞) < ζ ω
    · exact Or.inl (h.1 r hr)
    · push Not at hr; exact Or.inr (h.2 r hr)
  have hbdr : ∀ r : ℝ≥0, s < r → r ≤ t → ∀ᵐ ω ∂Q, |u ((r : ℝ), Z r ω)| ≤ C' := fun r hr hrt =>
    (hOκ r).mono fun ω h => by
      rcases h with h | h
      · exact hC' _ ⟨⟨by exact_mod_cast hr, by exact_mod_cast hrt⟩, h⟩
      · rw [h, hu0, abs_zero]; exact hC0
  -- the terminal value
  have hψm : AEStronglyMeasurable (fun ω => u ((t : ℝ), Z t ω)) Q :=
    dk_aestronglyMeasurable_killed (((hZ.adapted t).measurable).mono (𝓖.le t) le_rfl) hO
      (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun x hx => ⟨⟨hstR, le_rfl⟩, hx⟩) (hu0 _) (hOκ t)
  have hψi : Integrable (fun ω => u ((t : ℝ), Z t ω)) Q :=
    Integrable.of_bound hψm C' ((hbdr t hst le_rfl).mono fun ω h => by
      rwa [Real.norm_eq_abs])
  -- the window averages
  set F : ℕ → Ω → ℝ := fun k => windowAvg (χs k) u Z t with hFdef
  have hFm : ∀ k, AEStronglyMeasurable (F k) Q := fun k =>
    (hψm.sub (hW k).1).congr (ae_of_all _ fun ω => by simp [hFdef])
  have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Z r ω) ∧
      ((∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) ∧ ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ) ∧
      (Z s ω ∈ O → ContinuousWithinAt u (Ioc (s : ℝ) t ×ˢ O) ((s : ℝ), Z s ω)) := by
    filter_upwards [hZ.continuous, hpath, hcs] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖F k ω‖ ≤ C' := fun k => hgood.mono fun ω h => by
    rw [Real.norm_eq_abs]
    refine abs_windowIntegral_le (hχ k) hs0 (h1 k) (h3 k).le fun r hr => ?_
    by_cases hr' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω
    · exact hC' _ ⟨hr, h.2.1.1 _ hr'⟩
    · push Not at hr'; rw [h.2.1.2 _ hr', hu0, abs_zero]; exact hC0
  have hlimF : ∀ᵐ ω ∂Q, Tendsto (fun k => F k ω) atTop (𝓝 (u ((s : ℝ), Z s ω))) :=
    hgood.mono fun ω h => by
      have hfc := dk_continuousOn_killed hcont hu0 hlin h.1 h.2.1.1 h.2.1.2
      refine tendsto_windowIntegral hs0 hfc ?_ hχ h1 h3 hlim
      have hpc : Continuous fun r : ℝ => (r, Z r.toNNReal ω) :=
        continuous_id.prodMk (h.1.comp continuous_real_toNNReal)
      by_cases hsζ : (s : ℝ≥0∞) < ζ ω
      · have hZs : Z s ω ∈ O := h.2.1.1 s hsζ
        set W : Set ℝ := {r | ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω} with hW
        have hWo : IsOpen W := isOpen_lt
          (ENNReal.continuous_coe.comp continuous_real_toNNReal) continuous_const
        have hsW : (s : ℝ) ∈ W := by simpa [hW] using hsζ
        have hp : Tendsto (fun r : ℝ => (r, Z r.toNNReal ω)) (𝓝[>] (s : ℝ))
            (𝓝[Ioc (s : ℝ) t ×ˢ O] ((s : ℝ), Z s ω)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have := (hpc.tendsto (s : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (s : ℝ)))
            simpa only [Real.toNNReal_coe] using this
          · filter_upwards [Ioo_mem_nhdsGT hstR,
              mem_nhdsWithin_of_mem_nhds (hWo.mem_nhds hsW)] with r hr hrW
            exact ⟨⟨hr.1, hr.2.le⟩, h.2.1.1 _ hrW⟩
        exact (h.2.2 hZs).tendsto.comp hp
      · push Not at hsζ
        rw [h.2.1.2 s hsζ, hu0]
        refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r hr => ?_)
        have hr0 : (0 : ℝ) ≤ r := hs0.trans (le_of_lt hr)
        have : s ≤ r.toNNReal := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact le_of_lt hr
        show 0 = u (r, Z r.toNNReal ω)
        rw [h.2.1.2 _ (hsζ.trans (by exact_mod_cast this)), hu0]
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
### Killed duality for `C^{0,2}` functions (time mollification)
-/

section C02

variable {ut : ℝ × (Fin d → ℝ) → ℝ} {u1 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ}
  {u2 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ}

/-- **Killed duality under `C^{0,2}` regularity**, from a positive time `s` to `t`. -/
theorem dk_duality_C02_killed (hZ : IsTestMPSolution Q 𝓖 b a O Z) (hO : IsOpen O)
    (hb : ContinuousOn b O) (ha : ContinuousOn a O) (hsym : ∀ y ∈ O, ∀ i j, a y i j = a y j i)
    {t : ℝ≥0} (hd : IsC02On u ut u1 u2 (Ioo 0 (t : ℝ) ×ˢ O))
    (hpde : ∀ p ∈ Ioo 0 (t : ℝ) ×ˢ O, spGen b a ut u1 u2 p = 0)
    (hcont : ContinuousOn u (Ioc 0 (t : ℝ) ×ˢ O))
    {C : ℝ} (hC : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ O, |u p| ≤ C)
    {κ : Fin d → ℝ} (hκ : κ ∉ O) (hu0 : ∀ r, u (r, κ) = 0) {Lc : ℝ}
    (hlin : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ O, |u p| ≤ Lc * ‖p.2 - κ‖) {ζ : Ω → ℝ≥0∞}
    (hpath : ∀ᵐ ω ∂Q, (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω → Z r ω ∈ O) ∧
      ∀ r : ℝ≥0, ζ ω ≤ r → Z r ω = κ)
    {s : ℝ≥0} (hs0 : 0 < s) (hst : s < t) :
    Integrable (fun ω => u ((t : ℝ), Z t ω)) Q ∧ Integrable (fun ω => u ((s : ℝ), Z s ω)) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q := by
  have hZ' := hZ.isMPSolutionOn hO hb ha hsym
  set C' := max C 0 with hC'def
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC' : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ O, |u p| ≤ C' := fun p hp => (hC p hp).trans
    (le_max_left _ _)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  set εs : ℕ → ℝ := fun n => (s : ℝ) / ((n : ℝ) + 2) with hεs
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hε0 : ∀ n, 0 < εs n := fun n => div_pos hsR (hn2 n)
  have hεs' : ∀ n, εs n < s := fun n => by
    simp only [hεs]
    rw [div_lt_iff₀ (hn2 n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hεlim : Tendsto εs atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  set v : ℕ → ℝ × (Fin d → ℝ) → ℝ := fun n => tconv (bwdMollifier (εs n)) u with hv
  have hφ : ∀ n, IsBwdMollifier (bwdMollifier (εs n)) (εs n) := fun n =>
    isBwdMollifier_bwdMollifier (hε0 n)
  have hsubIoo : ∀ n, Ioo (s : ℝ) t ×ˢ O ⊆ Ioo (0 + εs n) t ×ˢ O := fun n =>
    prod_mono (Ioo_subset_Ioo_left (by linarith [hεs' n])) le_rfl
  have hsubIoc : ∀ n, Ioc (s : ℝ) t ×ˢ O ⊆ Ioc (0 + εs n) t ×ˢ O := fun n =>
    prod_mono (Ioc_subset_Ioc_left (by linarith [hεs' n])) le_rfl
  have hvc : ∀ n, ContinuousOn (v n) (Ioc (0 + εs n) t ×ˢ O) := fun n =>
    continuousOn_tconv (hφ n).continuous (hφ n).support_subset hO hcont
  have hvC : ∀ n, ∀ p ∈ Ioc (0 + εs n) (t : ℝ) ×ˢ O, |v n p| ≤ C' := fun n p hp =>
    abs_tconv_le_of_bound (hφ n) hcont hC' hp
  have hv0 : ∀ n r, v n (r, κ) = 0 := fun n r => by simp [hv, tconv, hu0]
  have hvlin : ∀ n, ∀ p ∈ Ioc (s : ℝ) t ×ˢ O, |v n p| ≤ Lc * ‖p.2 - κ‖ := fun n p hp => by
    have hp' := hsubIoc n hp
    exact (hφ n).abs_tconv_le (hcont.comp (by fun_prop) fun r hr => mem_Ioc_prod_of_shift hp' hr)
      fun r hr => hlin _ (mem_Ioc_prod_of_shift hp' hr)
  have hOκ : ∀ r : ℝ≥0, ∀ᵐ ω ∂Q, Z r ω ∈ O ∨ Z r ω = κ := fun r => hpath.mono fun ω h => by
    by_cases hr : (r : ℝ≥0∞) < ζ ω
    · exact Or.inl (h.1 r hr)
    · push Not at hr; exact Or.inr (h.2 r hr)
  have hDn : ∀ n, _ := fun n => dk_duality_setIntegral_killed hZ' hO hb ha hst
    (u := v n) ((hd.contDiffOn_tconv hO (hφ n)).mono (by simpa using hsubIoo n))
    (fun p hp => hd.stGen_tconv_eq_zero hO hpde (hφ n) (hε0 n).le
      (by simpa using hsubIoo n hp))
    ((hvc n).mono (hsubIoc n))
    (ae_of_all _ fun ω hω => ((hvc n) _ ⟨⟨by linarith [hεs' n], hst.le⟩, hω⟩).mono
      (hsubIoc n))
    hκ (hv0 n) (hvlin n) (fun p hp => hvC n p (hsubIoc n hp)) hpath
  -- limits
  have hlim : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t → ∀ᵐ ω ∂Q,
      Tendsto (fun n => v n ((r : ℝ), Z r ω)) atTop (𝓝 (u ((r : ℝ), Z r ω))) := by
    intro r hr hrt
    filter_upwards [hOκ r] with ω hω
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    rcases hω with hω | hω
    · exact tendsto_tconv_bwdMollifier hcont hε0 hεlim ⟨⟨hr0, hrt⟩, hω⟩
    · rw [hω, hu0]; simp only [hv0]; exact tendsto_const_nhds
  have hbnd : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t → ∀ n, ∀ᵐ ω ∂Q,
      |v n ((r : ℝ), Z r ω)| ≤ C' := by
    intro r hr hrt n
    filter_upwards [hOκ r] with ω hω
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    rcases hω with hω | hω
    · exact hvC n _ ⟨⟨by linarith [hεs' n], hrt⟩, hω⟩
    · rw [hω, hv0, abs_zero]; exact hC0
  have hTt := tendsto_setIntegral_of_abs_le (fun n => (hDn n).1.aestronglyMeasurable)
    (hbnd t hstR.le le_rfl) (hlim t hstR.le le_rfl)
  have hTs := tendsto_setIntegral_of_abs_le (fun n => (hDn n).2.1.aestronglyMeasurable)
    (hbnd s le_rfl hstR.le) (hlim s le_rfl hstR.le)
  have hint : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
      (∀ n, AEStronglyMeasurable (fun ω => v n ((r : ℝ), Z r ω)) Q) →
      Integrable (fun ω => u ((r : ℝ), Z r ω)) Q := by
    intro r hr hrt hm
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    refine Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop hm (hlim r hr hrt)) C' ?_
    filter_upwards [hOκ r] with ω hω
    rw [Real.norm_eq_abs]
    rcases hω with hω | hω
    · exact hC' _ ⟨⟨hr0, hrt⟩, hω⟩
    · rw [hω, hu0, abs_zero]; exact hC0
  refine ⟨hint t hstR.le le_rfl fun n => (hDn n).1.aestronglyMeasurable,
    hint s le_rfl hstR.le fun n => (hDn n).2.1.aestronglyMeasurable, fun A hA => ?_⟩
  refine tendsto_nhds_unique (hTt A) ((hTs A).congr fun n => ?_)
  exact ((hDn n).2.2 A hA).symm

end C02

end BlockBand.Diffusion
