module

public import BlockBand.Statements
public import BlockBand.Endpoints.LaplaceLimit
public import BlockBand.Endpoints.LaplaceDetermination
public import BlockBand.Counting.SimpleSpectralLimitsTopology

/-!
# From Laplace bounds to convergence of the critical limit laws as `τ ↓ 0`

This file turns bounds on Laplace functionals into convergence to the sine law as `τ ↓ 0`, using
tightness from uniform first moments and the fact that Laplace functionals determine the law.

## Main results

* `se_criticalSequence`: an explicit critical sequence (`W_j = j+1`, `n_j = max 4 ⌈τ(j+1)⌉`)
  for every `τ > 0`.
* `se_spectralLaplace_markedLaw`: the spectral Laplace functional of the finite marked law is
  `E exp(-Σ_α f(u_α))`, `u_α = Nρ(λ_α - E)` of the spectral realization.
* `se_tendsto_spectralLaplace`: weak convergence of marked laws implies convergence of the
  spectral Laplace functionals (the spectral projection is continuous).
* `se_moment_of_unitIntensity`: unit spectral intensity bounds the first moments.
* `se_tendsto_sineLaw`: uniform first moments (tightness, Prokhorov) and convergence of the
  Laplace functionals to the sine Laplace functional give convergence to the sine law as
  `τ ↓ 0` (unique cluster point, Laplace determination).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open BlockBand.Model.Construction (stateCutoff stateCutoff_mem_unitInterval
  continuous_vaguePointMeasure_coordinate vaguePointMeasure_t2Space)

/-- `n_j/W_j → τ` for `W_j = j + 1`, `n_j = max 4 ⌈τ(j+1)⌉`. -/
theorem sel_ratio_tendsto (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun j : ℕ => ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 τ) := by
  have hup : Tendsto (fun j : ℕ => τ + 5 * (1 / ((j : ℝ) + 1))) atTop (𝓝 τ) := by
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (h0.const_mul (5 : ℝ)).const_add τ
    simpa using h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun j => ?_) (fun j => ?_)
  · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    rw [le_div_iff₀ hj]
    have h1 : τ * ((j : ℝ) + 1) ≤ (⌈τ * ((j : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈τ * ((j : ℝ) + 1)⌉₊ : ℝ) ≤ ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    linarith
  · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_le_iff₀ hj]
    have h1 : (⌈τ * ((j : ℝ) + 1)⌉₊ : ℝ) < τ * ((j : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : ((max 4 ⌈τ * ((j : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ 4 + (⌈τ * ((j : ℝ) + 1)⌉₊ : ℝ) := by
      rcases le_total 4 ⌈τ * ((j : ℝ) + 1)⌉₊ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈τ * ((j : ℝ) + 1)⌉₊]
    have : 5 * (1 / ((j : ℝ) + 1)) * ((j : ℝ) + 1) = 5 := by field_simp
    nlinarith

/-- Tightness of an arbitrary family from uniform first moments. -/
theorem sel_isTight {ι : Type*} (P : ι → ProbabilityMeasure (VaguePointMeasure ℝ))
    (hcount : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ g x) →
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ N, ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure)
        ∂(P N : Measure (VaguePointMeasure ℝ)) ≤ C) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (VaguePointMeasure ℝ)) :
      Measure (VaguePointMeasure ℝ)) | μ ∈ Set.range P} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose C hCfin hC using fun n : ℕ =>
    hcount (stateCutoff ℝ n) (fun x => (stateCutoff_mem_unitInterval ℝ n x).1)
  let c : ℕ → ℝ := fun n => (C n).toReal / (ε' n : ℝ) + 1
  refine ⟨_, isCompact_cutoffBox c, ?_⟩
  rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
  let A : ℕ → Set (VaguePointMeasure ℝ) := fun n =>
    {ξ | ENNReal.ofReal (c n) ≤ ENNReal.ofReal (ξ.coordinate (stateCutoff ℝ n))}
  have hsub : {ξ : VaguePointMeasure ℝ | ∀ n, ξ.coordinate (stateCutoff ℝ n) ≤ c n}ᶜ ⊆
      ⋃ n, A n := by
    intro ξ hξ
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hξ
    obtain ⟨n, hn⟩ := hξ
    exact mem_iUnion.2 ⟨n, ENNReal.ofReal_le_ofReal hn.le⟩
  have hbound : ∀ n, (P N : Measure (VaguePointMeasure ℝ)) (A n) ≤ ε' n := by
    intro n
    have hpos : (0 : ℝ) < ε' n := hε'pos n
    have hc0 : 0 < c n := by
      have : 0 ≤ (C n).toReal / (ε' n : ℝ) := div_nonneg ENNReal.toReal_nonneg hpos.le
      dsimp only [c]
      linarith
    have hmeas : AEMeasurable (fun ξ : VaguePointMeasure ℝ =>
        ENNReal.ofReal (ξ.coordinate (stateCutoff ℝ n))) (P N : Measure (VaguePointMeasure ℝ)) :=
      (ENNReal.measurable_ofReal.comp
        (continuous_vaguePointMeasure_coordinate (stateCutoff ℝ n)).measurable).aemeasurable
    refine (meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.2 hc0).ne'
      ENNReal.ofReal_ne_top).trans ?_
    refine ENNReal.div_le_of_le_mul ((hC n N).trans ?_)
    rw [← ENNReal.ofReal_toReal (hCfin n), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have heq : (ε' n : ℝ) * c n = (C n).toReal + ε' n := by
      dsimp only [c]
      field_simp
    linarith
  calc (P N : Measure (VaguePointMeasure ℝ))
        {ξ : VaguePointMeasure ℝ | ∀ n, ξ.coordinate (stateCutoff ℝ n) ≤ c n}ᶜ
      ≤ (P N : Measure (VaguePointMeasure ℝ)) (⋃ n, A n) := measure_mono hsub
    _ ≤ ∑' n, (P N : Measure (VaguePointMeasure ℝ)) (A n) := measure_iUnion_le _
    _ ≤ ∑' n, (ε' n : ℝ≥0∞) := ENNReal.tsum_le_tsum hbound
    _ ≤ ε := hε'sum.le

/-- A critical sequence for every ratio `τ > 0`. -/
def se_criticalSequence (τ : ℝ) (hτ : 0 < τ) : CriticalSequence τ where
  n j := max 4 ⌈τ * ((j : ℝ) + 1)⌉₊
  W j := j + 1
  n_ge_four _ := le_max_left _ _
  W_pos _ := Nat.succ_pos _
  width_tendsto := tendsto_add_atTop_nat 1
  ratio_tendsto := sel_ratio_tendsto τ hτ

/-- The spectral Laplace functional of the marked law of a finite realization. -/
theorem se_spectralLaplace_markedLaw {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(spectralProjectionLaw (R.markedLaw E) : Measure (VaguePointMeasure ℝ)) =
      ∫ H, Real.exp (-∑ α, f (R.spectral.unfoldedEigenvalue E H α))
        ∂(R.model.law : Measure p.SiteMatrix) := by
  have hproj := BlockBand.Counting.continuous_markedSpectralProjection
  have hcont : Continuous fun ξ : VaguePointMeasure ℝ => Real.exp (-∫ x, f x ∂ξ.measure) :=
    Real.continuous_exp.comp
      (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate f).neg
  unfold spectralProjectionLaw FiniteRealization.markedLaw
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    integral_map hproj.measurable.aemeasurable hcont.aestronglyMeasurable,
    integral_map (R.spectral.measurable_markedConfig E).aemeasurable
      (f := fun ξ : MarkedPointMeasure => Real.exp (-∫ x, f x ∂ξ.spectralProjection.measure))
      (hcont.comp hproj).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [R.spectral.markedConfig_ae E] with H hH
  simp only [MarkedPointMeasure.spectralProjection]
  rw [(R.spectral.markedConfig E H).spectral_eq, hH,
    integral_map measurable_fst.aemeasurable (f := fun x : ℝ => f x)
      f.continuous.aestronglyMeasurable,
    integral_finsetSum_measure (f := fun x : ℝ × MassProfile => f x.1)
      (fun α _ => integrable_dirac'
      (f.continuous.measurable.comp measurable_fst).stronglyMeasurable enorm_lt_top)]
  congr 2
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_dirac' (fun x : ℝ × MassProfile => f x.1) _
    (f.continuous.measurable.comp measurable_fst).stronglyMeasurable]
  rfl

/-- Weak convergence of marked laws gives convergence of the spectral Laplace functionals. -/
theorem se_tendsto_spectralLaplace {ι : Type*} {l : Filter ι}
    {P : ι → ProbabilityMeasure MarkedPointMeasure} {Q : ProbabilityMeasure MarkedPointMeasure}
    (h : Tendsto P l (𝓝 Q)) (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun j => ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(spectralProjectionLaw (P j) : Measure (VaguePointMeasure ℝ))) l
      (𝓝 (∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(spectralProjectionLaw Q : Measure (VaguePointMeasure ℝ)))) := by
  have hT : Continuous fun ν : ProbabilityMeasure (VaguePointMeasure ℝ) =>
      ∫ ξ, laplaceTest f hf ξ ∂(ν : Measure (VaguePointMeasure ℝ)) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (laplaceTest f hf)
  have hM : Continuous fun ν : ProbabilityMeasure MarkedPointMeasure => spectralProjectionLaw ν :=
    ProbabilityMeasure.continuous_map BlockBand.Counting.continuous_markedSpectralProjection
  exact ((hT.comp hM).tendsto Q).comp h

/-- Unit spectral intensity bounds the first moments of the spectral projection. -/
theorem se_moment_of_unitIntensity {ν : ProbabilityMeasure MarkedPointMeasure}
    (h : HasUnitSpectralIntensity ν) (g : CompactlySupportedContinuousMap ℝ ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure)
        ∂(spectralProjectionLaw ν : Measure (VaguePointMeasure ℝ)) ≤
      ENNReal.ofReal (∫ x, g x) := by
  have hproj := BlockBand.Counting.continuous_markedSpectralProjection
  have hc : Continuous fun ξ : VaguePointMeasure ℝ => ENNReal.ofReal (∫ x, g x ∂ξ.measure) :=
    ENNReal.continuous_ofReal.comp (continuous_vaguePointMeasure_coordinate g)
  unfold spectralProjectionLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hc.measurable hproj.measurable]
  simp only [MarkedPointMeasure.spectralProjection]
  have hid := h g
  have hnn : ∀ ξ : MarkedPointMeasure, 0 ≤ ∫ x, g x ∂ξ.spectral.measure :=
    fun ξ => integral_nonneg hg
  have hm : AEStronglyMeasurable (fun ξ : MarkedPointMeasure => ∫ x, g x ∂ξ.spectral.measure)
      (ν : Measure MarkedPointMeasure) :=
    ((continuous_vaguePointMeasure_coordinate g).comp hproj).aestronglyMeasurable
  by_cases hI : Integrable (fun ξ : MarkedPointMeasure => ∫ x, g x ∂ξ.spectral.measure)
      (ν : Measure MarkedPointMeasure)
  · rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hnn), hid]
  · have h0 := integral_undef hI
    rw [hid] at h0
    have hg0 : ∀ x, g x = 0 := by
      have hint : Integrable g := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => hg x) hint).1 h0
      intro x
      exact congrFun (Continuous.ae_eq_iff_eq volume g.continuous continuous_const |>.1 hae) x
    have : ∀ ξ : MarkedPointMeasure, ∫ x, g x ∂ξ.spectral.measure = 0 := fun ξ => by
      simp [hg0]
    simp [this]

/-- **Convergence to the sine law** from uniform first moments and convergence of the Laplace
functionals to the sine Laplace functional, along `τ ↓ 0`. -/
theorem se_tendsto_sineLaw {Q : PositiveRatio → ProbabilityMeasure (VaguePointMeasure ℝ)}
    (hmom : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ g x) → ∀ τ,
      ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure) ∂(Q τ : Measure (VaguePointMeasure ℝ)) ≤
        ENNReal.ofReal (∫ x, g x))
    (hlap : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      Tendsto (fun τ => ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(Q τ : Measure (VaguePointMeasure ℝ)))
        atBot (𝓝 (sineLaplaceFunctional f)))
    (sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ)) (hsine : IsSineLaw sineLaw) :
    Tendsto Q atBot (𝓝 sineLaw) := by
  have := vaguePointMeasure_t2Space ℝ
  have hcpt := isCompact_closure_of_isTightMeasureSet
    (sel_isTight Q fun g hg => ⟨ENNReal.ofReal (∫ x, g x), ENNReal.ofReal_ne_top, hmom g hg⟩)
  refine hcpt.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun τ => subset_closure (mem_range_self τ)) ?_
  intro Q' _ hQ'
  apply vaguePointMeasureLaw_eq_of_laplace
  intro f hf
  rw [hsine.2 f hf]
  let T : ProbabilityMeasure (VaguePointMeasure ℝ) → ℝ := fun ν =>
    ∫ ξ, laplaceTest f hf ξ ∂(ν : Measure (VaguePointMeasure ℝ))
  have hT : Continuous T :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (laplaceTest f hf)
  have hlim : Tendsto T (Filter.map Q atBot) (𝓝 (sineLaplaceFunctional f)) :=
    tendsto_map'_iff.2 (hlap f hf)
  have hcl : ClusterPt Q' (Filter.map Q atBot) := hQ'
  have key : T Q' = sineLaplaceFunctional f :=
    eq_of_nhds_neBot (_root_.ClusterPt.map hcl hT.continuousAt hlim)
  exact key

end BlockBand.Endpoints
