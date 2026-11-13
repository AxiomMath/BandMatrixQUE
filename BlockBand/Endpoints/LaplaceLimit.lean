module

public import BlockBand.Endpoints.VagueCompactness
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Existence of a limiting law from convergent Laplace functionals

If the first moments of a sequence of laws of point measures on `ℝ` are uniformly bounded and
their Laplace functionals converge, then some limit law has the limiting Laplace functional
(`exists_law_of_tendsto_laplace`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open BlockBand.Model.Construction (stateCutoff stateCutoff_mem_unitInterval
  continuous_vaguePointMeasure_coordinate vaguePointMeasure_t2Space)

/-- The Laplace test `ξ ↦ exp (-∫ f dξ)` of a nonnegative `f ∈ C_c(ℝ, ℝ)`, as a bounded
continuous real function on the vague state space `VaguePointMeasure ℝ`
(values in `(0, 1]`). -/
def laplaceTest (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) :
    VaguePointMeasure ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ξ => Real.exp (-ξ.coordinate f),
      Real.continuous_exp.comp (continuous_vaguePointMeasure_coordinate f).neg⟩ 1
    (fun ξ η => by
      have h1 : ∀ ζ : VaguePointMeasure ℝ, Real.exp (-ζ.coordinate f) ≤ 1 := fun ζ =>
        Real.exp_le_one_iff.2 (neg_nonpos.2 (integral_nonneg hf))
      have h2 : ∀ ζ : VaguePointMeasure ℝ, 0 < Real.exp (-ζ.coordinate f) := fun ζ =>
        Real.exp_pos _
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;> linarith [h1 ξ, h1 η, h2 ξ, h2 η])

/-- Evaluation of the Laplace test: for nonnegative `f ∈ C_c(ℝ, ℝ)` and every point
measure `ξ`, `laplaceTest f hf ξ = exp (-∫ f dξ)`. -/
theorem laplaceTest_apply (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (ξ : VaguePointMeasure ℝ) :
    laplaceTest f hf ξ = Real.exp (-∫ x, f x ∂ξ.measure) :=
  rfl

/-- **Tightness from first moments.** If for every nonnegative `g ∈ C_c(ℝ, ℝ)` the first
moments `E_{P N} ξ(g)` (as `∫⁻ ofReal (∫ g dξ)`) are bounded uniformly in `N` by a finite
constant, then the family of laws `{P N : N ∈ ℕ}` on `VaguePointMeasure ℝ` is tight. -/
theorem isTightMeasureSet_of_lintegral_coordinate_le
    (P : ℕ → ProbabilityMeasure (VaguePointMeasure ℝ))
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

/-- **Existence of a limit law from Laplace functionals.** Let `P N` be laws on the
vague state space `VaguePointMeasure ℝ` such that, for every nonnegative `g ∈ C_c(ℝ, ℝ)`,
the first moments `∫⁻ ofReal (∫ g dξ) d(P N)` are bounded by a finite constant uniformly
in `N`, and such that for every nonnegative `f ∈ C_c(ℝ, ℝ)` the Laplace functionals
`∫ exp (-∫ f dξ) d(P N)` converge as `N → ∞` to `L f`. Then some law `Q` on
`VaguePointMeasure ℝ` (a weak cluster point of `P`) has Laplace functional exactly `L f`
for every nonnegative `f ∈ C_c(ℝ, ℝ)`. -/
theorem exists_law_of_tendsto_laplace (P : ℕ → ProbabilityMeasure (VaguePointMeasure ℝ))
    (hcount : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ g x) →
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ N, ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure)
        ∂(P N : Measure (VaguePointMeasure ℝ)) ≤ C)
    (L : CompactlySupportedContinuousMap ℝ ℝ → ℝ)
    (hL : ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
      Filter.Tendsto (fun N => ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(P N : Measure (VaguePointMeasure ℝ))) Filter.atTop (nhds (L f))) :
    ∃ Q : ProbabilityMeasure (VaguePointMeasure ℝ),
      ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
        ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(Q : Measure (VaguePointMeasure ℝ)) = L f := by
  have := vaguePointMeasure_t2Space ℝ
  have hcpt := isCompact_closure_of_isTightMeasureSet
    (isTightMeasureSet_of_lintegral_coordinate_le P hcount)
  obtain ⟨Q, -, hQ⟩ := hcpt (f := Filter.map P atTop)
    (tendsto_principal.2 (Eventually.of_forall fun N => subset_closure (mem_range_self N)))
  refine ⟨Q, fun f hf => ?_⟩
  let T : ProbabilityMeasure (VaguePointMeasure ℝ) → ℝ := fun ν =>
    ∫ ξ, laplaceTest f hf ξ ∂(ν : Measure (VaguePointMeasure ℝ))
  have hT : Continuous T :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (laplaceTest f hf)
  have hlim : Tendsto T (Filter.map P atTop) (𝓝 (L f)) := tendsto_map'_iff.2 (hL f hf)
  exact eq_of_nhds_neBot (hQ.map hT.continuousAt hlim)

end BlockBand.Endpoints
