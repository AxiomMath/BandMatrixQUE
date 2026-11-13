module

public import BlockBand.Layers.ScalarRecursion

/-!
# Matched path traces from the core bound: Steps 3–4 of the matched-traces theorem

The `path` clause (the matched-trace moments) of `MatchedTracesContract`, for every `1 ≤ r ≤ TW`
of both parities, from the core clause `r ∈ {1,2}` (`CoreTraceBound`, Steps 1–2), which is an
explicit hypothesis here.

Law: `pathLaw W r b`; `z = z_∂(E)`, `E ∈ bulkInterval κ`, `d(X) = matchedDistance b E X`,
`a_r = ‖d(X_r)‖_{L^p(pathLaw W r b)}`, `2 ≤ p ≤ ε₀ W`.

* One step in law (`srec_path_step`, `r ≥ 1`): under `pathLaw (r+2) = (layerLaw ⊗ pathLaw r) ∘
  pgGrow⁻¹` (`measurePreserving_pgGrow`) and a.s. `X_{r+2} = B*(A - E - X_r)⁻¹B`
  (`pathSchur_pgGrow`), pointwise
  `d(X_{r+2}) ≤ q d(X_r) + C W⁻² + excess + M₀ 1{d(X_r) > d₀}` with the crude bound
  `d ≤ M₀ = η⁻¹ + 1` on the exit event. Minkowski and Fubini (the excess has conditional
  `L^p` norm `≤ C√p/W` given the old path) give
  `a_{r+2} ≤ q a_r + C W⁻² + C√p/W + M₀ P(d(X_r) > d₀)^{1/p}`.
* The exit probability (the scalar exit bound, `srec_exit_core`) transferred to `pathLaw` through the
  law of the grown Schur matrix (`srec_path_tail`) is `≤ exp(-cW log W)`; for `p ≤ cW` its
  contribution is `≤ M₀/W`.
* Iterating from the cores `r₀ ∈ {1,2}` (geometric series, `q < 1`):
  `a_r ≤ (C_core + (2C + M₀)/(1-q)) √p/W`, uniformly in `r ≤ TW`. For `W < W₀`, the crude bound
  `a_r ≤ M₀ ≤ M₀ W₀ √p / W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- **Exit, in law**: the event `d(X_{r₀+2k}) > d'` under `pathLaw` has at most the probability of
the exit event of the growing path by step `k`. -/
theorem srec_path_tail {W : ℕ} {b : ℝ} (hb1 : b < 1 / 2) (E d' : ℝ) {r₀ : ℕ} (hr₀ : 1 ≤ r₀)
    (k : ℕ) :
    pathLaw W (r₀ + 2 * k) b {ω | d' < matchedDistance b E (pathSchur E ω)} ≤
      growthLaw W r₀ k b {ω | ∃ k' ≤ k, d' < matchedDistance b E (grownSchur E ω k')} := by
  have hmap := map_grownSchur_growthLaw_of_lt (W := W) (L := k) hb1 E hr₀ le_rfl
  have hS : MeasurableSet {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ |
      d' < matchedDistance b E X} :=
    measurableSet_lt measurable_const (srec_measurable_matchedDistance b E W)
  have hP := measurePreserving_pgPath (W := W) b hr₀ k k le_rfl
  have hae : AEMeasurable (fun ω : GrowthSample W r₀ k => grownSchur E ω k) (growthLaw W r₀ k b) :=
    ((measurable_pathSchur W (r₀ + 2 * k) E).comp hP.measurable).aemeasurable.congr
      ((ae_grownSchur_eq_pathSchur_of_lt hb1 E hr₀ le_rfl).mono fun ω h => h.symm)
  have h1 : pathLaw W (r₀ + 2 * k) b {ω | d' < matchedDistance b E (pathSchur E ω)} =
      ((pathLaw W (r₀ + 2 * k) b).map (pathSchur E))
        {X | d' < matchedDistance b E X} :=
    (Measure.map_apply (measurable_pathSchur W (r₀ + 2 * k) E) hS).symm
  rw [h1, ← hmap, Measure.map_apply_of_aemeasurable hae hS]
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
  exact ⟨k, le_rfl, hω⟩

/-- **One step of the recursion in law** (`r ≥ 1`): Minkowski over the decomposition
`d(X_{r+2}) ≤ q d(X_r) + C W⁻² + excess + M₀ 1{d(X_r) > d₀}` under `layerLaw ⊗ pathLaw r`. -/
theorem srec_path_step {W r : ℕ} {b q C d₀ M0 E p B : ℝ} (hb1 : b < 1 / 2) (hr : 1 ≤ r)
    (hq0 : 0 ≤ q) (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0) (hp : 1 ≤ p)
    (hcr : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ M0)
    (hex : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      eLpNorm (fun ω => srecExcess b E q C d₀ W X (layerSchur .separate E X ω))
        (ENNReal.ofReal p) (layerLaw W b .separate) ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω : PathSample W (r + 2) => matchedDistance b E (pathSchur E ω))
        (ENNReal.ofReal p) (pathLaw W (r + 2) b) ≤
      ENNReal.ofReal q * eLpNorm (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω))
          (ENNReal.ofReal p) (pathLaw W r b) +
        ENNReal.ofReal (C / (W : ℝ) ^ 2) + ENNReal.ofReal B +
        ENNReal.ofReal M0 *
          pathLaw W r b {ω | d₀ < matchedDistance b E (pathSchur E ω)} ^ (1 / p) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have hpr : IsProbabilityMeasure (pathLaw W r b) := by unfold pathLaw; infer_instance
  have hp0' : 0 < p := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0'
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  set μ := (layerLaw W b .separate).prod (pathLaw W r b) with hμ
  have hMP := measurePreserving_pgGrow (W := W) b hr
  have hd := srec_measurable_matchedDistance b E W
  have hD : Measurable (fun ω : PathSample W (r + 2) => matchedDistance b E (pathSchur E ω)) :=
    hd.comp (measurable_pathSchur _ _ E)
  have hDr : Measurable (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω)) :=
    hd.comp (measurable_pathSchur _ _ E)
  rw [← eLpNorm_comp_measurePreserving hD.aestronglyMeasurable hMP]
  set S := {ω : PathSample W r | d₀ < matchedDistance b E (pathSchur E ω)} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hDr
  set f1 : LayerSample W .separate × PathSample W r → ℝ :=
    fun x => q * matchedDistance b E (pathSchur E x.2) with hf1
  set f2 : LayerSample W .separate × PathSample W r → ℝ := fun _ => C / (W : ℝ) ^ 2 with hf2
  set f3 : LayerSample W .separate × PathSample W r → ℝ := fun x =>
    srecExcess b E q C d₀ W (pathSchur E x.2) (layerSchur .separate E (pathSchur E x.2) x.1)
    with hf3
  set f4 : LayerSample W .separate × PathSample W r → ℝ :=
    (Prod.snd ⁻¹' S).indicator (fun _ => M0) with hf4
  have hbound : ∀ᵐ x ∂μ,
      ‖((fun ω : PathSample W (r + 2) => matchedDistance b E (pathSchur E ω)) ∘ pgGrow) x‖ ≤
        f1 x + f2 x + f3 x + f4 x := by
    have h1 : ∀ᵐ x ∂μ, IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det :=
      (measurePreserving_snd (μ := layerLaw W b .separate)
        (ν := pathLaw W r b)).quasiMeasurePreserving.ae (ae_isUnit_det_pathMatrix W r hb1 E)
    have h2 : ∀ᵐ x ∂μ, IsUnit (pathMatrix (pgGrow x) - (E : ℂ) • 1).det :=
      hMP.quasiMeasurePreserving.ae (ae_isUnit_det_pathMatrix W (r + 2) hb1 E)
    have h3 : ∀ᵐ x ∂μ, (pathSchur E (pgGrow x)).IsHermitian :=
      hMP.quasiMeasurePreserving.ae (srec_ae_pathSchur_isHermitian W (r + 2) b E)
    filter_upwards [h1, h2, h3] with x hH hG hherm
    obtain ⟨ℓ, ω⟩ := x
    have hS := (isUnit_det_pgGrow_iff hr E ℓ ω hH).mp hG
    have heq := pathSchur_pgGrow hr E ℓ ω hH hS
    have hcrY := hcr _ hherm
    simp only [Function.comp_apply]
    have hY0 : 0 ≤ matchedDistance b E (pathSchur E (pgGrow (ℓ, ω))) :=
      (norm_nonneg _).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg hY0]
    rw [heq] at hcrY ⊢
    have hdX0 : 0 ≤ matchedDistance b E (pathSchur E ω) := (norm_nonneg _).trans (le_max_left _ _)
    have hf3nn := srec_excess_nonneg b E q C d₀ W (pathSchur E ω)
      (layerSchur .separate E (pathSchur E ω) ℓ)
    have hW2 : 0 ≤ C / (W : ℝ) ^ 2 := by positivity
    simp only [hf1, hf2, hf3, hf4]
    by_cases hdX : matchedDistance b E (pathSchur E ω) ≤ d₀
    · have hnot : (ℓ, ω) ∉ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, not_lt]; exact hdX
      rw [Set.indicator_of_notMem hnot]
      have : srecExcess b E q C d₀ W (pathSchur E ω) (layerSchur .separate E (pathSchur E ω) ℓ) =
          max (matchedDistance b E (layerSchur .separate E (pathSchur E ω) ℓ) -
            q * matchedDistance b E (pathSchur E ω) - C / (W : ℝ) ^ 2) 0 := by
        simp only [srecExcess, hdX, ↓reduceIte]
      rw [this]
      have := le_max_left (matchedDistance b E (layerSchur .separate E (pathSchur E ω) ℓ) -
        q * matchedDistance b E (pathSchur E ω) - C / (W : ℝ) ^ 2) 0
      linarith
    · have hmem : (ℓ, ω) ∈ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq]; exact not_le.mp hdX
      rw [Set.indicator_of_mem hmem]
      have := mul_nonneg hq0 hdX0
      linarith
  have hf1e : eLpNorm f1 (ENNReal.ofReal p) μ = ENNReal.ofReal q *
      eLpNorm (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω))
        (ENNReal.ofReal p) (pathLaw W r b) := by
    have : f1 = q • ((fun ω : PathSample W r => matchedDistance b E (pathSchur E ω)) ∘
        Prod.snd) := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hq0,
      eLpNorm_comp_measurePreserving hDr.aestronglyMeasurable measurePreserving_snd]
  have hf2e : eLpNorm f2 (ENNReal.ofReal p) μ = ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
    rw [hf2, eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg (by positivity)]
  have hf3e : eLpNorm f3 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B := by
    refine srec_eLpNorm_prod_le (srec_measurable_excess_comp b E q C d₀) hp0' ?_
    filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with y hy
    exact hex _ hy
  have hf4e : eLpNorm f4 (ENNReal.ofReal p) μ =
      ENNReal.ofReal M0 * pathLaw W r b S ^ (1 / p) := by
    rw [hf4, eLpNorm_indicator_const (hSm.preimage measurable_snd).nullMeasurableSet hp0
      ENNReal.ofReal_ne_top, measurePreserving_snd.measure_preimage hSm.nullMeasurableSet,
      ENNReal.toReal_ofReal hp0'.le, Real.enorm_of_nonneg hM0]
  calc eLpNorm ((fun ω : PathSample W (r + 2) => matchedDistance b E (pathSchur E ω)) ∘ pgGrow)
        (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun x => f1 x + f2 x + f3 x + f4 x) (ENNReal.ofReal p) μ :=
        eLpNorm_mono_ae_real (hD.comp hMP.measurable).aestronglyMeasurable hbound
    _ ≤ eLpNorm f1 (ENNReal.ofReal p) μ + eLpNorm f2 (ENNReal.ofReal p) μ +
          eLpNorm f3 (ENNReal.ofReal p) μ + eLpNorm f4 (ENNReal.ofReal p) μ := by
        refine (eLpNorm_add_le (f := fun x => f1 x + f2 x + f3 x) (g := f4) hp1).trans ?_
        refine add_le_add ?_ le_rfl
        refine (eLpNorm_add_le (f := fun x => f1 x + f2 x) (g := f3) hp1).trans ?_
        exact add_le_add (eLpNorm_add_le (f := f1) (g := f2) hp1) le_rfl
    _ ≤ _ := by
        rw [hf1e, hf2e, hf4e]
        exact add_le_add (add_le_add le_rfl hf3e) le_rfl

/-- Every `r ≥ 1` is `r₀ + 2k` with a core `r₀ ∈ {1, 2}`. -/
theorem srec_core_decomp {r : ℕ} (hr : 1 ≤ r) :
    ∃ r₀ k : ℕ, (r₀ = 1 ∨ r₀ = 2) ∧ r = r₀ + 2 * k := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' r
  · exact ⟨2, k - 1, Or.inr rfl, by omega⟩
  · exact ⟨1, k, Or.inl rfl, by omega⟩

/-- **The matched-trace moments** for every `1 ≤ r ≤ TW` (Steps 3–4 of the proof of the
matched-traces theorem): the exact type of the `path` field of `MatchedTracesContract`, from the
core clause `CoreTraceBound` (`r ∈ {1,2}`), `ConditionalBlockGUECount` and
`GaussianLpGradient`. -/
theorem matchedTracesPath_of_core
    (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) (hcore : CoreTraceBound) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
            ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
          (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, hex⟩ := srec_excess_core hcount hgrad b hb0 hb1 κ hκ
  obtain ⟨εc, Cc, hεc, hcb⟩ := hcore b hb0 hb1 κ hκ
  obtain ⟨d₁, hd₁, hexit⟩ := srec_exit_core hcount hgrad hcore b hb0 hb1 κ T hκ
  obtain ⟨c, W₀, hc, hexitW⟩ := hexit (min d₀ d₁) (lt_min hd₀ hd₁) (min_le_right _ _)
  obtain ⟨η, hη, hηE⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  set M0 := η⁻¹ + 1 with hM0def
  have hM0 : 0 ≤ M0 := by positivity
  set ε₀ := min (min ε εc) c with hε₀def
  set Cc' := max Cc 0 with hCc'
  set C' := 2 * C + M0 with hC'def
  have h1q : 0 < 1 - q := by linarith
  set Cfin := Cc' + C' / (1 - q) with hCfin
  have hCc'0 : 0 ≤ Cc' := le_max_right _ _
  have hCfin0 : 0 ≤ Cfin := by positivity
  refine ⟨ε₀, max Cfin (M0 * W₀), lt_min (lt_min hε hεc) hc, ?_⟩
  intro W hW p hp2 hpε r hr hrT E hE
  obtain ⟨hzη, hEabs⟩ := hηE E hE
  have hz0 : 0 < (boundaryZ b E).im := hη.trans_le hzη
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hp0 : 0 < p := by linarith
  have hpe : p ≤ ε * W := hpε.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) hWr.le)
  have hpc : p ≤ εc * W := hpε.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) hWr.le)
  have hpcW : p ≤ c * W := hpε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
  have hsp : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  set x := Real.sqrt p / W with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxW : 1 / (W : ℝ) ≤ x := div_le_div_of_nonneg_right hsp hWr.le
  have hxW2 : 1 / (W : ℝ) ^ 2 ≤ x := by
    refine le_trans ?_ hxW
    exact one_div_le_one_div_of_le hWr (by nlinarith)
  -- crude bound
  have hcrX : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ M0 := by
    intro X hX
    refine (srec_matchedDistance_le hEabs hz0 hX).trans ?_
    have := inv_anti₀ hη hzη
    linarith
  have hcrude : ∀ r' : ℕ, eLpNorm (fun ω : PathSample W r' => matchedDistance b E (pathSchur E ω))
      (ENNReal.ofReal p) (pathLaw W r' b) ≤ ENNReal.ofReal M0 := by
    intro r'
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have hpr : IsProbabilityMeasure (pathLaw W r' b) := by unfold pathLaw; infer_instance
    refine (eLpNorm_le_of_ae_bound (C := M0) ((srec_measurable_matchedDistance b E W).comp
      (measurable_pathSchur W r' E)).aestronglyMeasurable ?_).trans ?_
    · filter_upwards [srec_ae_pathSchur_isHermitian W r' b E] with ω hω
      have h0 : 0 ≤ matchedDistance b E (pathSchur E ω) := (norm_nonneg _).trans (le_max_left _ _)
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg h0]
      exact hcrX _ hω
    · rw [measure_univ, ENNReal.one_rpow, one_mul]
  show eLpNorm (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω))
      (ENNReal.ofReal p) (pathLaw W r b) ≤ _
  by_cases hWW : W₀ ≤ W
  swap
  · -- small `W`: the crude bound
    refine (hcrude r).trans (ENNReal.ofReal_le_ofReal ?_)
    have hW₀ : (W : ℝ) ≤ W₀ := by exact_mod_cast (not_le.mp hWW).le
    calc M0 = M0 * 1 := (mul_one _).symm
      _ ≤ M0 * W₀ * Real.sqrt p / W := by
          rw [mul_assoc, mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hM0
          rw [le_div_iff₀ hWr, one_mul]
          nlinarith
      _ ≤ max Cfin (M0 * W₀) * Real.sqrt p / W := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.sqrt_nonneg _)) hWr.le
  -- the exit contribution
  have hexitP : ∀ r' : ℕ, 1 ≤ r' → (r' : ℝ) ≤ T * W →
      ENNReal.ofReal M0 *
          pathLaw W r' b {ω | d₀ < matchedDistance b E (pathSchur E ω)} ^ (1 / p) ≤
        ENNReal.ofReal (M0 * x) := by
    intro r' hr' hr'T
    obtain ⟨r₀, k, hr₀, rfl⟩ := srec_core_decomp hr'
    have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
    have hP : pathLaw W (r₀ + 2 * k) b {ω | d₀ < matchedDistance b E (pathSchur E ω)} ≤
        ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) := by
      refine (measure_mono fun ω hω => ?_).trans ((srec_path_tail hb1 E (min d₀ d₁) hr₀1 k).trans
        (hexitW W hWW hW r₀ hr₀ k (by exact_mod_cast hr'T) E hE))
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact lt_of_le_of_lt (min_le_left _ _) hω
    have hexp : Real.exp (-(c * W * Real.log W)) ^ (1 / p) ≤ 1 / (W : ℝ) := by
      rw [← Real.exp_mul]
      have hlog : 0 ≤ Real.log W := Real.log_nonneg hW1
      have h1 : -(c * W * Real.log W) * (1 / p) ≤ -Real.log W := by
        have hcp : 1 ≤ c * W / p := by rw [le_div_iff₀ hp0]; linarith
        have : -(c * W * Real.log W) * (1 / p) = -(Real.log W * (c * W / p)) := by
          field_simp
        rw [this, neg_le_neg_iff]
        nlinarith
      calc Real.exp (-(c * W * Real.log W) * (1 / p)) ≤ Real.exp (-Real.log W) :=
            Real.exp_le_exp.mpr h1
        _ = 1 / (W : ℝ) := by rw [Real.exp_neg, Real.exp_log hWr, one_div]
    calc ENNReal.ofReal M0 *
          pathLaw W (r₀ + 2 * k) b {ω | d₀ < matchedDistance b E (pathSchur E ω)} ^ (1 / p)
        ≤ ENNReal.ofReal M0 * ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) ^ (1 / p) := by
          gcongr
      _ = ENNReal.ofReal (M0 * Real.exp (-(c * W * Real.log W)) ^ (1 / p)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
            ← ENNReal.ofReal_mul hM0]
      _ ≤ ENNReal.ofReal (M0 * x) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hexp.trans hxW) hM0)
  -- the recursion
  have hrec : ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W →
      eLpNorm (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω))
        (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (Cfin * x) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro hr hrT
    by_cases hr2 : r ≤ 2
    · have hcr : r = 1 ∨ r = 2 := by omega
      refine (hcb W hW p hp2 hpc r hcr E hE).trans (ENNReal.ofReal_le_ofReal ?_)
      have hle : Cc ≤ Cfin := by
        have h1 : 0 ≤ C' / (1 - q) := by positivity
        have h2 := le_max_left Cc 0
        linarith
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hle hx0
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    have hr' : 1 ≤ r' := by omega
    have hr'T : (r' : ℝ) ≤ T * W := le_trans (by exact_mod_cast (by omega : r' ≤ r' + 2)) hrT
    have hih := ih r' (by omega) hr' hr'T
    have hstep := srec_path_step (W := W) (r := r') (B := C * Real.sqrt p / W) hb1 hr' hq0 hC0 hM0
      (by linarith) hcrX (fun X hX => hex W hW X hX E hE p hp2 hpe)
    refine hstep.trans ?_
    have hqa : ENNReal.ofReal q * eLpNorm (fun ω : PathSample W r' =>
        matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal p) (pathLaw W r' b) ≤
        ENNReal.ofReal (q * (Cfin * x)) := by
      rw [ENNReal.ofReal_mul hq0]; gcongr
    have hCW : C / (W : ℝ) ^ 2 ≤ C * x := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hxW2 hC0
    calc _ ≤ ENNReal.ofReal (q * (Cfin * x)) + ENNReal.ofReal (C * x) + ENNReal.ofReal (C * x) +
          ENNReal.ofReal (M0 * x) := by
          refine add_le_add (add_le_add (add_le_add hqa (ENNReal.ofReal_le_ofReal hCW)) ?_)
            (hexitP r' hr' hr'T)
          rw [hxdef, mul_div_assoc]
      _ = ENNReal.ofReal (q * (Cfin * x) + C * x + C * x + M0 * x) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (Cfin * x) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hkey : q * Cfin + C' ≤ Cfin := by
            have : (1 - q) * Cfin = (1 - q) * Cc' + C' := by
              rw [hCfin]; field_simp
            nlinarith [mul_nonneg h1q.le hCc'0]
          have : q * (Cfin * x) + C * x + C * x + M0 * x = (q * Cfin + C') * x := by
            rw [hC'def]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hkey hx0
  refine (hrec r hr hrT).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hxdef, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.sqrt_nonneg _)) hWr.le

end BlockBand.Layers
