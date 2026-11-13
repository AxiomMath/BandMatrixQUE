module

public import BlockBand.Endpoints.Poisson.PoissonEndpointDefs
public import BlockBand.Endpoints.Sine.SineEndpointLimit
public import BlockBand.Model.Construction.SpectralFiniteRealization
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Convergence to the unit Poisson law

We prove the limit clause of the Poisson endpoint theorem from the Poisson Laplace limit.

* `pe_cutoff`, `pe_exists_smooth_approx`: nonnegative `C^∞` `C_c` tests approximate every
  nonnegative `C_c` test uniformly, with supports in a fixed compact set (normed-bump
  convolution).
* `pe_isUnitPoissonLaw_of_smooth`: Poisson Laplace functionals at smooth tests imply
  `IsUnitPoissonLaw` (the characterization quantifies over all nonnegative `C_c` tests).
* `pe_tendsto_poissonLaw`: uniform first moments and Laplace convergence at smooth tests give
  `Q τ → poissonLaw` as `τ → ∞` (tightness via `sel_isTight`, Prokhorov, unique cluster point).
* `poissonEndpointLimit_of_laplace`: `PoissonEndpointLaplace → PoissonEndpointLimitClause`, for
  every critical family (the critical-limit convergence and unit-intensity conjuncts of
  `IsCriticalFamily`). Tightness uses the unit intensity, where the paper uses the factorial
  count bounds; for `IsCriticalFamily` this is part of the definition.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution

/-- A nonnegative `C_c` cutoff equal to one on `[-M, M]`. -/
theorem pe_cutoff (M : ℝ) (hM : 0 ≤ M) :
    ∃ u : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ u x) ∧ ∀ x, |x| ≤ M → u x = 1 := by
  let φ : ContDiffBump (0 : ℝ) := ⟨M + 1, M + 2, by linarith, by linarith⟩
  refine ⟨⟨⟨φ, φ.continuous⟩, φ.hasCompactSupport⟩, fun x => φ.nonneg, fun x hx => ?_⟩
  change φ x = 1
  apply φ.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |x| ≤ M + 1
  linarith

/-- **Smooth approximation of a test.** A nonnegative `C_c` function `f` vanishing off `[-L, L]` is
within `ε` (uniformly) of a nonnegative `C^∞` `C_c` function vanishing off `[-(L+1), L+1]`
(convolution with a normed bump). -/
theorem pe_exists_smooth_approx (f : CompactlySupportedContinuousMap ℝ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (L : ℝ) (hL : ∀ x, L < |x| → f x = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CompactlySupportedContinuousMap ℝ ℝ, ContDiff ℝ ∞ (g : ℝ → ℝ) ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x, |g x - f x| ≤ ε) ∧ ∀ x, L + 1 < |x| → g x = 0 := by
  obtain ⟨r₀, hr₀, hunif⟩ :=
    Metric.uniformContinuous_iff.1 (CompactlySupportedContinuousMapClass.uniformContinuous f) ε hε
  set r : ℝ := min r₀ 1 with hr_def
  have hr : 0 < r := lt_min hr₀ one_pos
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  set G : ℝ → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : ℝ → ℝ)
    with hG_def
  have hGs : ContDiff ℝ ∞ G :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ (φ.contDiff_normed (n := ⊤))
      f.continuous.locallyIntegrable
  have hGapply : ∀ x, G x = ∫ t, φ.normed volume t * f (x - t) := fun x => by
    rw [hG_def, convolution_def]; rfl
  have hGzero : ∀ x, L + 1 < |x| → G x = 0 := by
    intro x hx
    rw [hGapply]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : |t| < r
    · have h1 : L < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        have : r ≤ 1 := min_le_right _ _
        linarith
      simp [hL _ h1]
    · have : φ.normed volume t = 0 := by
        rw [← Function.notMem_support, φ.support_normed_eq, Metric.mem_ball, Real.dist_eq,
          sub_zero]
        exact ht
      simp [this]
  have hGcs : HasCompactSupport G :=
    HasCompactSupport.intro (isCompact_Icc (a := -(L + 1)) (b := L + 1)) fun x hx => by
      apply hGzero
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact lt_abs.2 (Or.inr (by linarith))
      · exact lt_abs.2 (Or.inl hx)
  refine ⟨⟨⟨G, hGs.continuous⟩, hGcs⟩, hGs, fun x => ?_, fun x => ?_, hGzero⟩
  · change 0 ≤ G x
    rw [hGapply]
    exact integral_nonneg fun t => mul_nonneg (φ.nonneg_normed t) (hf0 _)
  · change |G x - f x| ≤ ε
    rw [← Real.dist_eq]
    refine φ.dist_normed_convolution_le f.continuous.aestronglyMeasurable fun y hy => ?_
    have hy' : dist y x < r₀ := by
      have : dist y x < r := hy
      exact lt_of_lt_of_le this (min_le_left _ _)
    exact (hunif hy').le

/-- **Smooth tests suffice for `IsUnitPoissonLaw`.** If a law has the Poisson Laplace functional
`exp(-∫(1 - e^{-g}))` at every nonnegative `C^∞` `C_c` test `g`, it has it at every nonnegative
`C_c` test (uniform smooth approximation, dominated convergence on both sides). -/
theorem pe_isUnitPoissonLaw_of_smooth (Q : ProbabilityMeasure (VaguePointMeasure ℝ))
    (h : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, ContDiff ℝ ∞ (g : ℝ → ℝ) → (∀ x, 0 ≤ g x) →
      ∫ ξ, Real.exp (-∫ x, g x ∂ξ.measure) ∂(Q : Measure (VaguePointMeasure ℝ)) =
        Real.exp (-∫ x, (1 - Real.exp (-g x)))) :
    IsUnitPoissonLaw Q := by
  intro f hf0
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, L < |x| → f x = 0 := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      f.hasCompactSupport.isCompact.isBounded
    refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
    by_contra hne
    have := hr (subset_tsupport f hne)
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_max_left r 0]
  obtain ⟨u, hu0, hu1⟩ := pe_cutoff (L + 1) (by linarith)
  choose g hgs hg0 hgf hgz using fun k : ℕ =>
    pe_exists_smooth_approx f hf0 L hL (1 / ((k : ℝ) + 1)) (by positivity)
  have hpt : ∀ k x, |g k x - f x| ≤ 1 / ((k : ℝ) + 1) * u x := by
    intro k x
    by_cases hx : |x| ≤ L + 1
    · rw [hu1 x hx, mul_one]; exact hgf k x
    · push Not at hx
      rw [hgz k x hx, hL x (by linarith), sub_self, abs_zero]
      exact mul_nonneg (by positivity) (hu0 x)
  have hεk : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hptl : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => hpt k x) ?_
    simpa using hεk.mul_const (u x)
  -- (i) the coordinates converge for every configuration
  have hcoord : ∀ ξ : VaguePointMeasure ℝ,
      Tendsto (fun k => ∫ x, g k x ∂ξ.measure) atTop (𝓝 (∫ x, f x ∂ξ.measure)) := by
    intro ξ
    have : IsFiniteMeasureOnCompacts ξ.measure := ⟨fun K hK => ξ.finite_on_compact K hK⟩
    have hi : ∀ φ : CompactlySupportedContinuousMap ℝ ℝ, Integrable φ ξ.measure := fun φ =>
      φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * ∫ x, u x ∂ξ.measure) atTop (𝓝 0) := by
      simpa using hεk.mul_const (∫ x, u x ∂ξ.measure)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hb0
    rw [← integral_sub (hi (g k)) (hi f), ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hi u).const_mul _) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hpt k x
  -- (ii) the Laplace functionals of `Q` converge
  have hlapQ : Tendsto (fun k => ∫ ξ, Real.exp (-∫ x, g k x ∂ξ.measure)
      ∂(Q : Measure (VaguePointMeasure ℝ))) atTop
      (𝓝 (∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(Q : Measure (VaguePointMeasure ℝ)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
      (integrable_const 1) (fun k => Eventually.of_forall fun ξ => ?_)
      (Eventually.of_forall fun ξ => ((Real.continuous_exp.tendsto _).comp (hcoord ξ).neg))
    · exact (Real.continuous_exp.comp
        (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate (g k)).neg
        ).aestronglyMeasurable
    · have h0 : 0 ≤ ∫ x, g k x ∂ξ.measure := integral_nonneg (hg0 k)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by linarith)
  -- (iii) the Poisson functionals converge
  have hpois : Tendsto (fun k => Real.exp (-∫ x, (1 - Real.exp (-g k x)))) atTop
      (𝓝 (Real.exp (-∫ x, (1 - Real.exp (-f x))))) := by
    refine (Real.continuous_exp.tendsto _).comp (Tendsto.neg ?_)
    refine tendsto_integral_of_dominated_convergence (fun x => u x) (fun k => ?_)
      (u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport)
      (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => tendsto_const_nhds.sub
        ((Real.continuous_exp.tendsto _).comp (hptl x).neg))
    · exact (continuous_const.sub (Real.continuous_exp.comp (g k).continuous.neg)
        ).aestronglyMeasurable
    · have h1 : Real.exp (-g k x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hg0 k x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      by_cases hx : |x| ≤ L + 1
      · rw [hu1 x hx]; linarith [Real.exp_pos (-g k x)]
      · push Not at hx
        rw [hgz k x hx, neg_zero, Real.exp_zero, sub_self]; exact hu0 x
  exact tendsto_nhds_unique (hlapQ.congr fun k => h (g k) (hgs k) (hg0 k)) hpois

/-- **Convergence to the unit Poisson law as `τ → ∞`** from uniform first moments and
convergence of the Laplace functionals at smooth tests (tightness, Prokhorov, unique cluster
point by `pe_isUnitPoissonLaw_of_smooth` and `isUnitPoissonLaw_unique`). -/
theorem pe_tendsto_poissonLaw {Q : PositiveRatio → ProbabilityMeasure (VaguePointMeasure ℝ)}
    (hmom : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ g x) → ∀ τ,
      ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure) ∂(Q τ : Measure (VaguePointMeasure ℝ)) ≤
        ENNReal.ofReal (∫ x, g x))
    (hlap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, ContDiff ℝ ∞ (f : ℝ → ℝ) →
      (∀ x, 0 ≤ f x) →
      Tendsto (fun τ => ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(Q τ : Measure (VaguePointMeasure ℝ)))
        atTop (𝓝 (Real.exp (-∫ x, (1 - Real.exp (-f x))))))
    (poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ)) (hpois : IsUnitPoissonLaw poissonLaw) :
    Tendsto Q atTop (𝓝 poissonLaw) := by
  have := BlockBand.Model.Construction.vaguePointMeasure_t2Space ℝ
  have hcpt := isCompact_closure_of_isTightMeasureSet
    (sel_isTight Q fun g hg => ⟨ENNReal.ofReal (∫ x, g x), ENNReal.ofReal_ne_top, hmom g hg⟩)
  refine hcpt.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun τ => subset_closure (mem_range_self τ)) ?_
  intro Q' _ hQ'
  refine isUnitPoissonLaw_unique (pe_isUnitPoissonLaw_of_smooth Q' fun f hfs hf => ?_) hpois
  let T : ProbabilityMeasure (VaguePointMeasure ℝ) → ℝ := fun ν =>
    ∫ ξ, laplaceTest f hf ξ ∂(ν : Measure (VaguePointMeasure ℝ))
  have hT : Continuous T :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (laplaceTest f hf)
  have hlim : Tendsto T (Filter.map Q atTop) (𝓝 (Real.exp (-∫ x, (1 - Real.exp (-f x))))) :=
    tendsto_map'_iff.2 (hlap f hfs hf)
  have hcl : ClusterPt Q' (Filter.map Q atTop) := hQ'
  have key : T Q' = Real.exp (-∫ x, (1 - Real.exp (-f x))) :=
    eq_of_nhds_neBot (_root_.ClusterPt.map hcl hT.continuousAt hlim)
  exact key

/-- **Convergence to the unit Poisson law for every family with the critical convergence and
unit intensity**, from the Poisson Laplace limit: if `family τ` is the
limit of the physical marked laws along every critical sequence and realization (the convergence
conjunct of `IsCriticalFamily` and of `IsJointRecoveryFamily`) and has unit spectral intensity,
then `spectralProjectionLaw (family τ) → poissonLaw` as `τ → ∞`. -/
theorem pe_tendsto_poisson_of_conv (h : PoissonEndpointLaplace) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E) (hE' : E < 2)
    (family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure)
    (hconv : ∀ (τ : PositiveRatio) (s : CriticalSequence τ.1)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
        Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 (family τ)))
    (hint : ∀ τ, HasUnitSpectralIntensity (family τ))
    (poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ)) (hpois : IsUnitPoissonLaw poissonLaw) :
    Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atTop (𝓝 poissonLaw) := by
  refine pe_tendsto_poissonLaw (fun g hg τ => se_moment_of_unitIntensity (hint τ) g hg) ?_
    poissonLaw hpois
  intro f hfs hf0
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨τ₀, hτ₀⟩ := h b hb hb' E hE hE' f hfs hf0 (η / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (⟨max τ₀ 1, by positivity⟩ : PositiveRatio)] with τ hτ
  have hττ₀ : τ₀ ≤ τ.1 := le_trans (le_max_left _ _) hτ
  let s := se_criticalSequence τ.1 τ.2
  let Rr : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
    BlockBand.Model.Construction.constructFiniteRealization _
  have hlim := se_tendsto_spectralLaplace (hconv τ s Rr) f hf0
  simp_rw [se_spectralLaplace_markedLaw] at hlim
  have hbd := le_of_tendsto ((hlim.sub_const (Real.exp (-∫ x, (1 - Real.exp (-f x))))).abs)
    (hτ₀ τ.1 hττ₀ s Rr)
  rw [Real.dist_eq]
  linarith

/-- **The limit clause of the Poisson endpoint theorem** from the Poisson Laplace limit: for
every critical family (`IsCriticalFamily`) the spectral projections converge to the unit
Poisson law as `τ → ∞`. Only the convergence and unit-intensity conjuncts of `IsCriticalFamily`
are used. -/
theorem poissonEndpointLimit_of_laplace (h : PoissonEndpointLaplace) :
    PoissonEndpointLimitClause := by
  intro b hb hb' E hE hE' family hfam poissonLaw hpois
  obtain ⟨-, -, hconv, -, hint, -⟩ := hfam
  exact pe_tendsto_poisson_of_conv h b hb hb' E hE hE' family hconv hint poissonLaw hpois

end BlockBand.Endpoints
