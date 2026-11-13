module

public import BlockBand.Endpoints.Normalization.VanishingBlockAtomMarked

/-!
# Vanishing block atoms: passage to a critical marked limit

The limit part of the vanishing block-atom bound, in three lemmas:

* `integrable_and_eventually_integral_le_of_tendsto`: if `μ_j → μ` weakly and `F ≥ 0` is
  continuous with `sup_j E_{μ_j} F² ≤ B`, then `F ∈ L¹(μ)` and eventually
  `E_{μ_j} F ≤ E_μ F + ε` (truncation at level `M`, tail `≤ B/M`: the count-moment step).
* `ae_measure_singleton_ne_zero`: a locally finite integer-valued measure on a metrizable,
  second-countable, locally compact space is carried by its atoms.
* `tendsto_integral_atomFunctional_of_diffuse`: if a.s. every atom of `ξ` carries a nonatomic
  mark (as the `diffuse` clause of the small-critical theorem provides; here a hypothesis on
  the given law), then `E_P ∫ |w(u)| Q_m(ν) ξ(du,dν) → 0` as `m → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology Set TopologicalSpace
open BlockBand.Model.Construction
open scoped ENNReal

/-- The truncation `min(F, M)` of a nonnegative continuous functional, as a bounded continuous
function. -/
def truncBCF {Ω : Type*} [TopologicalSpace Ω] (F : Ω → ℝ) (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) (M : ℝ) (hM : 0 ≤ M) : BoundedContinuousFunction Ω ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun ξ => min (F ξ) M, hF.min continuous_const⟩ M
    (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor
      · have := le_min (hF0 x) hM
        have := min_le_right (F y) M
        linarith
      · have := le_min (hF0 y) hM
        have := min_le_right (F x) M
        linarith)

theorem truncBCF_apply {Ω : Type*} [TopologicalSpace Ω] (F : Ω → ℝ) (hF : Continuous F)
    (hF0 : ∀ ξ, 0 ≤ F ξ) (M : ℝ) (hM : 0 ≤ M) (ξ : Ω) :
    truncBCF F hF hF0 M hM ξ = min (F ξ) M := rfl

/-- **Count-moment passage to the limit.** If `μ_j → μ` weakly, `F ≥ 0` is continuous and
`E_{μ_j} F² ≤ B` for all `j`, then `F` is `μ`-integrable and, for every `ε > 0`, eventually
`E_{μ_j} F ≤ E_μ F + ε`. -/
theorem integrable_and_eventually_integral_le_of_tendsto {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) (F : Ω → ℝ) (hF : Continuous F) (hF0 : ∀ ξ, 0 ≤ F ξ)
    (B : ℝ) (hint : ∀ j, Integrable (fun ξ => F ξ ^ 2) (μs j : Measure Ω))
    (hB : ∀ j, (∫ ξ, F ξ ^ 2 ∂(μs j : Measure Ω)) ≤ B) :
    Integrable F (μ : Measure Ω) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        (∫ ξ, F ξ ∂(μs j : Measure Ω)) ≤ (∫ ξ, F ξ ∂(μ : Measure Ω)) + ε := by
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
  -- integrability of `F` under every `μ_j`
  have hintj : ∀ j, Integrable F (μs j : Measure Ω) := by
    intro j
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add (hint j)) hF.aestronglyMeasurable
    filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (F ξ - 1)]
  -- uniform bound on the truncated expectations
  have htrunc_le : ∀ (M : ℝ) (hM : 0 ≤ M) (j : ℕ),
      (∫ ξ, truncBCF F hF hF0 M hM ξ ∂(μs j : Measure Ω)) ≤ 1 + B := by
    intro M hM j
    calc (∫ ξ, truncBCF F hF hF0 M hM ξ ∂(μs j : Measure Ω))
        ≤ ∫ ξ, (1 + F ξ ^ 2) ∂(μs j : Measure Ω) := by
          apply integral_mono ((truncBCF F hF hF0 M hM).integrable _)
            ((integrable_const (1 : ℝ)).add (hint j))
          intro ξ
          simp only [Pi.add_apply, truncBCF_apply]
          have := min_le_left (F ξ) M
          nlinarith [sq_nonneg (F ξ - 1)]
      _ = 1 + ∫ ξ, F ξ ^ 2 ∂(μs j : Measure Ω) := by
          rw [integral_add (integrable_const _) (hint j)]
          simp
      _ ≤ 1 + B := by linarith [hB j]
  -- integrability of `F` under `μ`
  have hFint : Integrable F (μ : Measure Ω) := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    have hsup : (fun ξ => ENNReal.ofReal (F ξ)) =
        fun ξ => ⨆ n : ℕ, ENNReal.ofReal (min (F ξ) n) := by
      funext ξ
      apply le_antisymm
      · obtain ⟨n, hn⟩ := exists_nat_ge (F ξ)
        exact le_iSup_of_le n (by rw [min_eq_left hn])
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    rw [hsup, lintegral_iSup]
    · apply lt_of_le_of_lt (b := ENNReal.ofReal (1 + B))
      · apply iSup_le
        intro n
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have heq : (∫⁻ ξ, ENNReal.ofReal (min (F ξ) n) ∂(μ : Measure Ω)) =
            ENNReal.ofReal (∫ ξ, truncBCF F hF hF0 n hn ξ ∂(μ : Measure Ω)) := by
          rw [ofReal_integral_eq_lintegral_ofReal ((truncBCF F hF hF0 n hn).integrable _)
            (Eventually.of_forall fun ξ => le_min (hF0 ξ) hn)]
          rfl
        rw [heq]
        apply ENNReal.ofReal_le_ofReal
        exact le_of_tendsto' (hconv (truncBCF F hF hF0 n hn)) (htrunc_le n hn)
      · exact ENNReal.ofReal_lt_top
    · intro n
      exact (hF.min continuous_const).measurable.ennreal_ofReal
    · intro n n' hnn' ξ
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnn'))
  refine ⟨hFint, ?_⟩
  intro ε hε
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun ξ => sq_nonneg (F ξ)) (hB 0)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hn
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have htail : B / n ≤ ε / 2 := by
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  have hlimT := hconv (truncBCF F hF hF0 n hn0)
  have hTle : (∫ ξ, truncBCF F hF hF0 n hn0 ξ ∂(μ : Measure Ω)) ≤ ∫ ξ, F ξ ∂(μ : Measure Ω) :=
    integral_mono ((truncBCF F hF hF0 n hn0).integrable _) hFint
      (fun ξ => by rw [truncBCF_apply]; exact min_le_left _ _)
  filter_upwards [hlimT.eventually_lt_const (by linarith :
    (∫ ξ, truncBCF F hF hF0 n hn0 ξ ∂(μ : Measure Ω)) <
      (∫ ξ, truncBCF F hF hF0 n hn0 ξ ∂(μ : Measure Ω)) + ε / 2)] with j hj
  have hpt : ∀ ξ, F ξ ≤ truncBCF F hF hF0 n hn0 ξ + F ξ ^ 2 / n := by
    intro ξ
    rw [truncBCF_apply]
    rcases le_total (F ξ) n with h | h
    · rw [min_eq_left h]
      have : 0 ≤ F ξ ^ 2 / n := div_nonneg (sq_nonneg _) hn0
      linarith
    · rw [min_eq_right h]
      have : F ξ ≤ F ξ ^ 2 / n := by
        rw [le_div_iff₀ hnpos]
        nlinarith [hF0 ξ]
      linarith [hn0]
  calc (∫ ξ, F ξ ∂(μs j : Measure Ω))
      ≤ ∫ ξ, (truncBCF F hF hF0 n hn0 ξ + F ξ ^ 2 / n) ∂(μs j : Measure Ω) :=
        integral_mono (hintj j) (((truncBCF F hF hF0 n hn0).integrable _).add
          ((hint j).div_const _)) hpt
    _ = (∫ ξ, truncBCF F hF hF0 n hn0 ξ ∂(μs j : Measure Ω)) +
          (∫ ξ, F ξ ^ 2 ∂(μs j : Measure Ω)) / n := by
        rw [integral_add ((truncBCF F hF hF0 n hn0).integrable _) ((hint j).div_const _),
          integral_div]
    _ ≤ (∫ ξ, truncBCF F hF hF0 n hn0 ξ ∂(μ : Measure Ω)) + ε / 2 + B / n := by
        have : (∫ ξ, F ξ ^ 2 ∂(μs j : Measure Ω)) / n ≤ B / n :=
          div_le_div_of_nonneg_right (hB j) hn0
        linarith
    _ ≤ (∫ ξ, F ξ ∂(μ : Measure Ω)) + ε := by linarith

/-- **Point measures are carried by their atoms:** for a locally finite integer-valued measure
on a metrizable, second-countable, locally compact space, almost every point is an atom. -/
theorem ae_measure_singleton_ne_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MetrizableSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] (ξ : VaguePointMeasure X) :
    ∀ᵐ x ∂ξ.measure, ξ.measure {x} ≠ 0 := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  rw [ae_iff]
  simp only [ne_eq, not_not]
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨R, hR, hRK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hKx
  have hfin : ξ.measure (Metric.cthickening R {x}) ≠ ⊤ := by
    rw [Metric.cthickening_singleton x hR.le]
    exact ne_top_of_le_ne_top (ξ.finite_on_compact K hK).ne (measure_mono hRK)
  have hT := tendsto_measure_cthickening (μ := ξ.measure) ⟨R, hR, hfin⟩
  rw [closure_singleton, hx] at hT
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ξ.measure (Metric.cthickening r {x}) < 1 :=
    hT.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp hev
  have hr : 0 < δ / 2 := by linarith
  have hlt := hδP (y := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; linarith)
  rw [Metric.cthickening_singleton x hr.le] at hlt
  refine ⟨Metric.closedBall x (δ / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hr), ?_⟩
  rcases ξ.integer_valued _ Metric.isClosed_closedBall.measurableSet with h | ⟨n, hn⟩
  · rw [h] at hlt
    exact absurd hlt (by simp)
  · rw [hn] at hlt ⊢
    have : n < 1 := by exact_mod_cast hlt
    have : n = 0 := by omega
    simp [this]

/-- **Diffuse limits kill the pair energy.** If `P`-a.s. every atom of the marked measure carries
a nonatomic mark, and the weight functional is `P`-integrable, then
`E_P ∫ |w(u)| Q_m(ν) ξ(du,dν) → 0` as `m → ∞`. -/
theorem tendsto_integral_atomFunctional_of_diffuse {w : ℝ → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) (P : ProbabilityMeasure MarkedPointMeasure)
    (hint : Integrable (markedFunctional (weightMarkTest hw hws)) (P : Measure MarkedPointMeasure))
    (hdiff : ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
      ξ.marked.measure {x} ≠ 0 → ∀ r : Torus, (x.2 : Measure Torus) {r} = 0) :
    Tendsto (fun m : ℕ => ∫ ξ, markedFunctional (atomMarkTest hw hws m) ξ
      ∂(P : Measure MarkedPointMeasure)) atTop (𝓝 0) := by
  have : BorelSpace MarkedSpectralSpace := markedSpectralSpace_borelSpace
  have hgint (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
      (ξ : MarkedPointMeasure) : Integrable g ξ.marked.measure :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have h0 : (0 : ℝ) = ∫ _ξ, (0 : ℝ) ∂(P : Measure MarkedPointMeasure) := by simp
  rw [h0]
  apply tendsto_integral_of_dominated_convergence (markedFunctional (weightMarkTest hw hws))
  · intro m
    exact (continuous_markedFunctional _).aestronglyMeasurable
  · exact hint
  · intro m
    filter_upwards with ξ
    have hnn : 0 ≤ markedFunctional (atomMarkTest hw hws m) ξ :=
      integral_nonneg (atomMarkTest_nonneg hw hws m)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono (hgint _ ξ) (hgint _ ξ) (atomMarkTest_le_weight hw hws m)
  · filter_upwards [hdiff] with ξ hξ
    have hz : (0 : ℝ) = ∫ _x, (0 : ℝ) ∂ξ.marked.measure := by simp
    rw [hz]
    apply tendsto_integral_of_dominated_convergence (weightMarkTest hw hws)
    · intro m
      exact (atomMarkTest hw hws m).continuous.aestronglyMeasurable
    · exact hgint _ ξ
    · intro m
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (atomMarkTest_nonneg hw hws m x)]
      exact atomMarkTest_le_weight hw hws m x
    · filter_upwards [ae_measure_singleton_ne_zero ξ.marked] with x hx
      have hQ := tendsto_pairEnergy_of_noAtoms x.2 (hξ x hx)
      have := hQ.const_mul |w x.1|
      simpa [atomMarkTest_apply] using this

end BlockBand.Endpoints.Normalization
