module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepPath
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Version
public import BlockBand.SourceProcess.Stochastic.SDE.Gronwall
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# No rank creation: positivity and stopped Gronwall

`stopped_eq_zero_of_barrier`: let `G` be a feasible Gram martingale-problem solution (sample space
in any universe), `f` a `C²` function of the Gram pair with `f ≥ 0` and `𝒢f ≤ C f` on feasible
states with `Re Tr M ≤ K`. If `f(G_0) = 0` a.s., then `f(G_{t∧σ_K}) = 0` a.s. for every `t`.

Fubini/progressive measurability: `IsGramMartingaleSolution` gives only adaptedness and a.s.
continuity. We use the jointly measurable version `jointVersion Y A` of `Y = toGramReal ∘ G`
(continuous paths on a measurable full-measure set `A`) and the raw
stopping time `ρ = rawHit {K ≤ Re Tr M} Y` (measurable, `= σ_K` on continuous paths), truncated to
`[0, B]` (`goodPath_bound`). On good paths this joint function is `F(s) = f(G_{s∧σ_K})`, so
`w(s) = E F(s)` is measurable and `w(t) ≤ E X_{t∧σ_K} + C ∫_0^t w = C ∫_0^t w`
(`goodPath_ineq`, `integral_gramItoProc_stopped`, `integral_integral_swap`); Gronwall
(`SDE.eq_zero_of_le_volterra`) gives `w = 0`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u

/-- **No increase of `f` from zero, up to the trace stop.** -/
theorem stopped_eq_zero_of_barrier {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {D0 : ℝ} {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) {C K : ℝ} (hC : 0 ≤ C)
    (hpos : ∀ H, GramFeasible D H → 0 ≤ f H)
    (hbar : ∀ H, GramFeasible D H → (H.1.trace).re ≤ K → gramGenerator D0 D f H ≤ C * f H)
    (h0 : ∀ᵐ ω ∂Q, f (G 0 ω) = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, f (stoppedProcess G (gramTraceStop G K) t ω) = 0 := by
  set Y : ℝ≥0 → Ω → Fin (gramDim c) → ℝ := fun t ω => toGramReal (G t ω) with hYdef
  have hYm : ∀ t, Measurable[𝓖 t] (Y t) := fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable (hG.adapted t)).measurable
  have hYm' : ∀ t, Measurable (Y t) := fun t => (hYm t).mono (𝓖.le t) le_rfl
  set ρ := rawHit (traceSuperLevel K) Y
  have hρ : IsStoppingTime 𝓖 ρ := isStoppingTime_rawHit hYm
  have hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω := by
    filter_upwards [hG.continuous] with ω hc
    exact continuous_toGramReal.comp hc
  obtain ⟨A, hA, hAQ, hAc⟩ := Uniqueness.exists_good_set hYc
  obtain ⟨B, hB0, hB⟩ := goodPath_bound hf hpos K
  set σ := gramTraceStop G K
  have hgood : ∀ᵐ ω ∂Q, GoodPath D f G ω ∧ ω ∈ A ∧ ρ ω = σ ω := by
    filter_upwards [hG.continuous, hG.feasible, h0, measure_eq_zero_iff_ae_notMem.1 hAQ]
      with ω hc hfe hz hωA
    refine ⟨⟨hc, hfe, hz⟩, by simpa using hωA, ?_⟩
    change rawHit (traceSuperLevel K) Y ω = gramTraceStop G K ω
    rw [rawHit_eq_hitTime (Y := Y) (isClosed_traceSuperLevel K) (continuous_toGramReal.comp hc)]
    exact hitTime_traceSuperLevel G K ω
  -- the truncated jointly measurable version of `F(s) = f(G_{s∧σ})`
  set hj : Ω → ℝ → ℝ := fun ω s => max 0 (min (f (fromGramReal (Uniqueness.jointVersion Y A
    ((stopTime (ρ ω) s.toNNReal : ℝ), ω)))) B) with hjdef
  have hmeas : Measurable (Function.uncurry hj) := by
    have hst : Measurable fun p : Ω × ℝ => ((stopTime (ρ p.1) p.2.toNNReal : ℝ), p.1) :=
      (Measurable.untopA ((WithTop.continuous_coe.measurable.comp
        (measurable_real_toNNReal.comp measurable_snd)).min
        (hρ.measurable'.comp measurable_fst))).coe_nnreal_real.prodMk measurable_fst
    exact measurable_const.max ((((contDiff_comp_fromGramReal hf).continuous.measurable.comp
      (Uniqueness.measurable_jointVersion hYm' hA hAc)).comp hst).min measurable_const)
  have hbd : ∀ ω s, ‖hj ω s‖ ≤ B := fun ω s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le hB0 (min_le_right _ _)
  have hjF : ∀ ω, GoodPath D f G ω ∧ ω ∈ A ∧ ρ ω = σ ω → ∀ s : ℝ,
      hj ω s = f (G (stopTime (σ ω) s.toNNReal) ω) := fun ω ⟨hω, hωA, hρσ⟩ s => by
    simp only [hjdef, Uniqueness.jointVersion_of_mem hωA, Real.toNNReal_coe, hρσ, hYdef,
      fromGramReal_toGramReal]
    obtain ⟨h1, h2⟩ := hB G ω hω s.toNNReal
    rw [min_eq_left h2, max_eq_right h1]
  -- integrability
  have hint : ∀ s, Integrable (fun ω => hj ω s) Q := fun s =>
    Integrable.of_bound (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (ae_of_all _ fun ω => hbd ω s)
  set w : ℝ → ℝ := fun s => ∫ ω, hj ω s ∂Q with hwdef
  have hw0 : ∀ s, 0 ≤ w s := fun s => integral_nonneg fun ω => le_max_left _ _
  have hwB : ∀ s, w s ≤ B := fun s => by
    refine (integral_mono (hint s) (integrable_const B) fun ω => ?_).trans (by simp)
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hbd ω s))
  have hwm : Measurable w :=
    (StronglyMeasurable.integral_prod_right (f := fun s ω => hj ω s)
      (hmeas.comp measurable_swap).stronglyMeasurable).measurable
  -- the integral inequality
  have hineq : ∀ t' : ℝ≥0, w t' ≤ C * ∫ s in Ioc (0 : ℝ) t', w s := by
    intro t'
    have hprod : Integrable (Function.uncurry hj) (Q.prod (volume.restrict (Ioc (0 : ℝ) t'))) :=
      Integrable.of_bound hmeas.aestronglyMeasurable B (ae_of_all _ fun p => hbd p.1 p.2)
    obtain ⟨hXi, hX0⟩ := integral_gramItoProc_stopped hD hG hf K t'
    have hle : (fun ω => hj ω t') ≤ᵐ[Q] fun ω =>
        stoppedProcess (gramItoProc D0 D f G) σ t' ω +
          C * ∫ s in Ioc (0 : ℝ) t', hj ω s := by
      filter_upwards [hgood] with ω hω
      rw [hjF ω hω, Real.toNNReal_coe,
        integral_congr_ae (ae_of_all _ fun s => hjF ω hω s)]
      exact goodPath_ineq hf hC hpos hbar hω.1 t'
    calc w t' ≤ ∫ ω, (stoppedProcess (gramItoProc D0 D f G) σ t' ω +
          C * ∫ s in Ioc (0 : ℝ) t', hj ω s) ∂Q :=
          integral_mono_ae (hint t') (hXi.add (hprod.integral_prod_left.const_mul C)) hle
      _ = C * ∫ ω, (∫ s in Ioc (0 : ℝ) t', hj ω s) ∂Q := by
          have e := integral_add hXi (hprod.integral_prod_left.const_mul C)
          simp only [Function.uncurry_apply_pair] at e
          rw [e, hX0, zero_add, integral_const_mul]
      _ = C * ∫ s in Ioc (0 : ℝ) t', w s := by rw [integral_integral_swap hprod]
  -- Gronwall
  have hii : IntervalIntegrable w volume 0 t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2 ?_
    exact Measure.integrableOn_of_bounded (M := B) (by simp) hwm.aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 s)]; exact hwB s)
  have hzero := SDE.eq_zero_of_le_volterra hC (fun s _ => hw0 s) hii (fun s hs => by
    rw [intervalIntegral.integral_of_le hs.1]
    have := hineq s.toNNReal
    rwa [Real.coe_toNNReal _ hs.1] at this) (t : ℝ) ⟨NNReal.coe_nonneg t, le_rfl⟩
  have hae : (fun ω => hj ω t) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => le_max_left _ _) (hint t)).1 hzero
  filter_upwards [hae, hgood] with ω h1 hω
  rw [stoppedProcess_eq_stopTime, ← Real.toNNReal_coe (r := t), ← hjF ω hω]
  exact h1

end BlockBand.SourceProcess.Stochastic.GramUniqueness
