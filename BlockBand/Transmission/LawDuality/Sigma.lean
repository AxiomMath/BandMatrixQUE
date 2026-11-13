module

public import BlockBand.Transmission.LawDuality.Moments

/-!
# Determination: the log-transforms generate the Giry σ-algebra

The log-transforms `G_{x_k}`, `x_k = 1/(k+2)`, generate the Giry σ-algebra on
`FiniteMeasure [0,1]`.

* **`measurable_of_logTransform`**: for any measurable space `α` and `ν : α → FiniteMeasure [0,1]`,
  `ν` is (Giry-)measurable as soon as every `a ↦ G_{x_k}(ν a)`, `x_k = 1/(k+2)`, is measurable.
* `measurable_logTransform`: conversely each `G_x` (`x ≥ 0`) is Giry-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

theorem measurable_logTransform {x : ℝ} (hx : 0 ≤ x) :
    Measurable fun ν : FiniteMeasure unitInterval => logTransform x ν := by
  have e : (fun ν : FiniteMeasure unitInterval => logTransform x ν) =
      fun ν => -Real.log (transmissionRatio ![x] ![0] ν) := by
    funext ν; rw [transmissionRatio_single_zero, Real.log_exp, neg_neg]
  rw [e]
  exact (Real.measurable_log.comp (measurable_transmissionRatio hx le_rfl zero_lt_one)).neg

theorem integral_polynomial_eq (p : Polynomial ℝ) (ν : FiniteMeasure unitInterval) :
    ∫ t, p.eval (t : ℝ) ∂(ν : Measure unitInterval) =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * moment i ν := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ fun i _ => (integrable_pow i ν).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, moment]

variable {α : Type*} [MeasurableSpace α] {ν : α → FiniteMeasure unitInterval}

theorem measurable_integral_continuous_of
    (h : ∀ k, Measurable fun a => logTransform (evalPoint k) (ν a)) (g : C(unitInterval, ℝ)) :
    Measurable fun a => ∫ t, g t ∂(ν a : Measure unitInterval) := by
  choose p hp using fun n : ℕ =>
    exists_polynomial_near_continuousMap 0 1 g (1 / ((n : ℝ) + 1)) (by positivity)
  have hpm : ∀ n, Measurable fun a => ∫ t, (p n).eval (t : ℝ) ∂(ν a : Measure unitInterval) := by
    intro n
    simp_rw [integral_polynomial_eq]
    exact Finset.measurable_sum _ fun i _ => (measurable_moment_of h i).const_mul _
  refine measurable_of_tendsto_metrizable hpm (tendsto_pi_nhds.2 fun a => ?_)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (ν a : Measure unitInterval).real univ)
      atTop (𝓝 (0 * (ν a : Measure unitInterval).real univ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
  rw [zero_mul] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  have hpi : Integrable (fun t : unitInterval => (p n).eval (t : ℝ)) (ν a : Measure unitInterval) :=
    (BoundedContinuousFunction.mkOfCompact ((p n).toContinuousMapOn (Set.Icc 0 1))).integrable _
  have hgi : Integrable (fun t : unitInterval => g t) (ν a : Measure unitInterval) :=
    (BoundedContinuousFunction.mkOfCompact g).integrable _
  rw [← integral_sub hpi hgi]
  refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun t => ?_)
  have := ContinuousMap.norm_coe_le_norm ((p n).toContinuousMapOn (Set.Icc 0 1) - g) t
  rw [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply] at this
  exact this.trans (hp n).le

/-- **The log-transforms at `x_k = 1/(k+2)` determine a measurable random finite measure.** -/
theorem measurable_of_logTransform
    (h : ∀ k, Measurable fun a => logTransform (evalPoint k) (ν a)) : Measurable ν := by
  have hc : Measurable fun a => (ν a : Measure unitInterval) := by
    refine Measurable.measure_of_isPiSystem (S := {s | IsClosed s})
      (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      (fun s hs => ?_) ?_
    · let g : ℕ → C(unitInterval, ℝ) := fun n =>
        ⟨fun t => ((IsClosed.apprSeq hs n t : ℝ≥0) : ℝ),
          NNReal.continuous_coe.comp (IsClosed.apprSeq hs n).continuous⟩
      refine measurable_of_tendsto_metrizable
        (fun n => ENNReal.measurable_ofReal.comp (measurable_integral_continuous_of h (g n)))
        (tendsto_pi_nhds.2 fun a => ?_)
      refine (HasOuterApproxClosed.tendsto_lintegral_apprSeq hs (ν a : Measure unitInterval)).congr
        fun n => ?_
      exact lintegral_coe_eq_integral _
        ((BoundedContinuousFunction.mkOfCompact (g n)).integrable _)
    · let g : C(unitInterval, ℝ) := ⟨fun _ => 1, continuous_const⟩
      have e : (fun a => (ν a : Measure unitInterval) univ) =
          fun a => ENNReal.ofReal (∫ t, g t ∂(ν a : Measure unitInterval)) := by
        funext a
        simp [g, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [e]
      exact ENNReal.measurable_ofReal.comp (measurable_integral_continuous_of h g)
  exact hc.subtype_mk

end BlockBand.Transmission.LawDuality
