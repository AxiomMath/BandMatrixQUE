module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Convergence together (Billingsley, Thm 3.2) on varying probability spaces

* `abs_integral_comp_sub_comp_le`: `|E F(Y) - E F(X)| ≤ L δ + C P(d(Y, X) ≥ δ)` for `F`
  `L`-Lipschitz with oscillation `≤ C` (outer measure; no measurability of the event needed).
* `tendstoInDistribution_of_forall_approx`: if `X_{i,N} ⇒ X_i` (`N → ∞`) for every `i`,
  `X_i ⇒ Z` along `l`, and `lim_{i,l} limsup_N P(d(Y_N, X_{i,N}) ≥ ε) = 0` for every `ε > 0`,
  then `Y_N ⇒ Z`.
* `tendstoInDistribution_of_tendsto_measure_dist`: the one-parameter case, `X_N ⇒ Z` and
  `P(d(Y_N, X_N) ≥ ε) → 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace BlockBand.Critical.Herglotz

/-- **Lipschitz comparison of expectations.** Law: two a.e.-measurable random variables `X, Y`
on one probability space `(Ω, μ)`, values in a pseudometric space `E` with opens measurable.
Test: `F : E → ℝ` `L`-Lipschitz with `|F x - F y| ≤ C` for all `x, y`. For every `δ ≥ 0`,
`|E F(Y) - E F(X)| ≤ L δ + C μ*(d(Y, X) ≥ δ)`, with `μ*` the outer measure (the event need not
be measurable). -/
theorem abs_integral_comp_sub_comp_le {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {F : E → ℝ} {C : ℝ} (hC : ∀ x y, dist (F x) (F y) ≤ C) {L : ℝ≥0} (hF : LipschitzWith L F)
    {X Y : Ω → E} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    |∫ ω, F (Y ω) ∂μ - ∫ ω, F (X ω) ∂μ| ≤
      L * δ + C * (μ {ω | δ ≤ dist (Y ω) (X ω)}).toReal := by
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := (dist_nonneg).trans (hC (X ω₀) (X ω₀))
  have hFc : Continuous F := hF.continuous
  have hbd : ∀ (W : Ω → E), AEMeasurable W μ → Integrable (fun ω => F (W ω)) μ := by
    intro W hW
    refine Integrable.of_bound (hFc.measurable.comp_aemeasurable hW).aestronglyMeasurable
      (‖F (X ω₀)‖ + C) (ae_of_all _ fun ω => ?_)
    have h1 := hC (W ω) (X ω₀)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (F (W ω)) (F (X ω₀))
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have hiY := hbd Y hY
  have hiX := hbd X hX
  set S := {ω | δ ≤ dist (Y ω) (X ω)} with hS
  rw [← integral_sub hiY hiX]
  refine (abs_integral_le_integral_abs).trans ?_
  have hnn : 0 ≤ᵐ[μ] fun ω => |F (Y ω) - F (X ω)| := ae_of_all _ fun _ => abs_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hiY.sub hiX).abs.aestronglyMeasurable]
  have hpt : ∀ ω, ENNReal.ofReal |F (Y ω) - F (X ω)| ≤
      ENNReal.ofReal (L * δ) + ENNReal.ofReal C * S.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      have := hC (Y ω) (X ω)
      rwa [Real.dist_eq] at this
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      have hlt : dist (Y ω) (X ω) < δ := by simpa [hS] using hω
      have := hF.dist_le_mul (Y ω) (X ω)
      rw [Real.dist_eq] at this
      calc |F (Y ω) - F (X ω)| ≤ L * dist (Y ω) (X ω) := this
        _ ≤ L * δ := mul_le_mul_of_nonneg_left hlt.le L.2
  have hlint : ∫⁻ ω, ENNReal.ofReal |F (Y ω) - F (X ω)| ∂μ ≤
      ENNReal.ofReal (L * δ) + ENNReal.ofReal C * μ S := by
    calc ∫⁻ ω, ENNReal.ofReal |F (Y ω) - F (X ω)| ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (L * δ) + ENNReal.ofReal C * S.indicator 1 ω) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (L * δ) + ENNReal.ofReal C * ∫⁻ ω, S.indicator 1 ω ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (L * δ) + ENNReal.ofReal C * μ S := by
          gcongr
          exact lintegral_indicator_one_le S
  have hfin : ENNReal.ofReal (L * δ) + ENNReal.ofReal C * μ S =
      ENNReal.ofReal (L * δ + C * (μ S).toReal) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hC0,
      ENNReal.ofReal_toReal (measure_ne_top μ S)]
  rw [hfin] at hlint
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint

set_option backward.isDefEq.respectTransparency.types false in
/-- **Convergence together, two-parameter form** (Billingsley, *Convergence of Probability
Measures*, Thm 3.2). Laws: `Y N` and `X i N` on probability spaces `(Ω N, P N)`, `X' i` on
`(Ω', P')`, `Z` on `(Ω'', P'')`; values in a pseudometric space `E` with its Borel σ-algebra.
Order of limits: `N → ∞` along a countably generated filter `u` first, then `i` along a filter
`l ≠ ⊥`. Hypotheses: `X i N ⇒ X' i` along `u` for every `i`; `X' i ⇒ Z` along `l`; and for all
`ε, η > 0`, eventually in `i`, eventually in `N`, the outer probability of
`{d(Y N, X i N) ≥ ε}` is `≤ η`. Conclusion: `Y N ⇒ Z` along `u`. -/
theorem tendstoInDistribution_of_forall_approx {κ ι E : Type*} {Ω : κ → Type*}
    [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω''] {P' : Measure Ω'}
    {P'' : Measure Ω''} [IsProbabilityMeasure P'] [IsProbabilityMeasure P'']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] {u : Filter κ}
    [u.IsCountablyGenerated] {l : Filter ι} [l.NeBot]
    {Y : ∀ N, Ω N → E} {X : ι → ∀ N, Ω N → E} {X' : ι → Ω' → E} {Z : Ω'' → E}
    (hY : ∀ N, AEMeasurable (Y N) (P N))
    (hX : ∀ i, TendstoInDistribution (X i) u (X' i) P P')
    (hX' : TendstoInDistribution X' l Z (fun _ => P') P'')
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ᶠ N in u,
      P N {ω | ε ≤ dist (Y N ω) (X i N ω)} ≤ ENNReal.ofReal η) :
    TendstoInDistribution Y u Z P P'' := by
  have hZ : AEMeasurable Z P'' := hX'.aemeasurable_limit
  refine ⟨hY, hZ, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨C, hC⟩ ⟨L, hF⟩
  have hFc : Continuous F := hF.continuous
  simp only [ProbabilityMeasure.coe_mk]
  -- rewrite the integrals on the sample spaces
  have hmapY : ∀ N, ∫ x, F x ∂(P N).map (Y N) = ∫ ω, F (Y N ω) ∂P N := fun N =>
    integral_map (hY N) hFc.aestronglyMeasurable
  have hmapZ : ∫ x, F x ∂P''.map Z = ∫ ω, F (Z ω) ∂P'' :=
    integral_map hZ hFc.aestronglyMeasurable
  simp_rw [hmapY, hmapZ]
  -- the bounded continuous function attached to `F`
  let Fb : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨F, hFc⟩ C hC
  have hlimX : ∀ i, Tendsto (fun N => ∫ ω, F (X i N ω) ∂P N) u (𝓝 (∫ ω, F (X' i ω) ∂P')) := by
    intro i
    have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (hX i).forall_aemeasurable (hX i).aemeasurable_limit).1 (hX i) Fb
    simpa [Fb] using h
  have hlimX' : Tendsto (fun i => ∫ ω, F (X' i ω) ∂P') l (𝓝 (∫ ω, F (Z ω) ∂P'')) := by
    have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hX'.forall_aemeasurable hZ).1 hX' Fb
    simpa [Fb] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ω₀⟩ : Nonempty Ω'' := nonempty_of_isProbabilityMeasure P''
  have hC0 : 0 ≤ C := (dist_nonneg).trans (hC (Z ω₀) (Z ω₀))
  set δ : ℝ := ε / (4 * ((L : ℝ) + 1)) with hδ
  set η : ℝ := ε / (4 * (C + 1)) with hη
  have hδ0 : 0 < δ := by positivity
  have hη0 : 0 < η := by positivity
  have hLδ : (L : ℝ) * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [L.2]
  have hCη : C * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨i, hi1, hi2⟩ := ((Metric.tendsto_nhds.1 hlimX' (ε / 4) (by positivity)).and
    (hclose δ hδ0 η hη0)).exists
  filter_upwards [Metric.tendsto_nhds.1 (hlimX i) (ε / 4) (by positivity), hi2] with N hN1 hN2
  have hcmp := abs_integral_comp_sub_comp_le hC hF ((hX i).forall_aemeasurable N) (hY N)
    hδ0.le
  have hμ : (P N {ω | δ ≤ dist (Y N ω) (X i N ω)}).toReal ≤ η :=
    ENNReal.toReal_le_of_le_ofReal hη0.le hN2
  have hCμ : C * (P N {ω | δ ≤ dist (Y N ω) (X i N ω)}).toReal ≤ C * η :=
    mul_le_mul_of_nonneg_left hμ hC0
  rw [Real.dist_eq] at hN1 hi1 ⊢
  calc |∫ ω, F (Y N ω) ∂P N - ∫ ω, F (Z ω) ∂P''|
      ≤ |∫ ω, F (Y N ω) ∂P N - ∫ ω, F (X i N ω) ∂P N| +
        |∫ ω, F (X i N ω) ∂P N - ∫ ω, F (X' i ω) ∂P'| +
        |∫ ω, F (X' i ω) ∂P' - ∫ ω, F (Z ω) ∂P''| := by
        have h1 := abs_sub_le (∫ ω, F (Y N ω) ∂P N) (∫ ω, F (X i N ω) ∂P N)
          (∫ ω, F (Z ω) ∂P'')
        have h2 := abs_sub_le (∫ ω, F (X i N ω) ∂P N) (∫ ω, F (X' i ω) ∂P')
          (∫ ω, F (Z ω) ∂P'')
        linarith
    _ < ε := by linarith

/-- **Convergence together, one-parameter form.** Laws: `Y N`, `X N` on `(Ω N, P N)`, `Z` on
`(Ω', P')`, values in a pseudometric space with its Borel σ-algebra; `u` countably generated.
If `X N ⇒ Z` and, for every `ε > 0`, the outer probability of `{d(Y N, X N) ≥ ε}` tends to `0`,
then `Y N ⇒ Z`. -/
theorem tendstoInDistribution_of_tendsto_measure_dist {κ E : Type*} {Ω : κ → Type*}
    [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] {u : Filter κ}
    [u.IsCountablyGenerated] {Y X : ∀ N, Ω N → E} {Z : Ω' → E}
    (hY : ∀ N, AEMeasurable (Y N) (P N)) (hX : TendstoInDistribution X u Z P P')
    (hclose : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => P N {ω | ε ≤ dist (Y N ω) (X N ω)}) u (𝓝 0)) :
    TendstoInDistribution Y u Z P P' := by
  refine tendstoInDistribution_of_forall_approx (l := (⊤ : Filter Unit)) (X := fun _ => X)
    (X' := fun _ => Z) hY (fun _ => hX) (tendstoInDistribution_const hX.aemeasurable_limit) ?_
  intro ε hε η hη
  refine Eventually.of_forall fun _ => ?_
  exact (hclose ε hε).eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hη))

end BlockBand.Critical.Herglotz
