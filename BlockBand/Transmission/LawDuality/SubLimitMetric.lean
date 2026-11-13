module

public import BlockBand.Transmission.LawDuality.SubLimitPath

/-!
# A moment metric on `FiniteMeasure [0,1]`, and the Lipschitz comparison bound

* `momentMetric` (a `def`, used as a local instance only):
  `d(ν, ν') = Σ_i min(2^{-i}, |m_i ν - m_i ν'|)`,
  the pull-back of Mathlib's `PiCountable` metric along the moment vector. Its topology is the
  weak topology **by definition** (`replaceTopology` with `isInducing_momentVec`), so
  bounded continuous tests and probability-measure topologies are unchanged.
* `dist_le_moments`: `d(ν, ν') ≤ Σ_{i<I} |m_i ν - m_i ν'| + 2·2^{-I}`.
* `dist_pi_le_moments`: the same for the sup metric on `Fin k → FM[0,1]`.
* `abs_integral_sub_le`: `|E f(Y) - E f(Y')| ≤ K r + C·P(B)` for a `K`-Lipschitz `f` with
  oscillation `≤ C`, when `d(Y, Y') ≤ r` off `B` (`B` need not be measurable).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality.SubLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

theorem momentTop_eq : (inferInstance : TopologicalSpace St) =
    (@PseudoMetricSpace.induced St (ℕ → ℝ) momentVec
      (PiCountable.pseudoMetricSpace (ι := ℕ) (F := fun _ => ℝ))).toUniformSpace.toTopologicalSpace :=
  isInducing_momentVec.eq_induced

/-- **The moment metric** (not a global instance). -/
@[instance_reducible] def momentMetric : PseudoMetricSpace St :=
  (@PseudoMetricSpace.induced St (ℕ → ℝ) momentVec
      (PiCountable.pseudoMetricSpace (ι := ℕ) (F := fun _ => ℝ))).replaceTopology momentTop_eq

theorem momentMetric_dist (ν ν' : St) : @dist St momentMetric.toDist ν ν' =
    ∑' i : ℕ, min (2⁻¹ ^ i) |moment i ν - moment i ν'| := by
  show @dist (ℕ → ℝ) PiCountable.dist _ _ = _
  rw [PiCountable.dist_eq_tsum]
  simp [Real.dist_eq, momentVec]

theorem dist_le_moments (ν ν' : St) (I : ℕ) : @dist St momentMetric.toDist ν ν' ≤
    ∑ i ∈ Finset.range I, |moment i ν - moment i ν'| + 2 * 2⁻¹ ^ I := by
  rw [momentMetric_dist]
  set f : ℕ → ℝ := fun i => min (2⁻¹ ^ i) |moment i ν - moment i ν'|
  have hf : Summable f := by
    have := @PiCountable.dist_summable ℕ _ (fun _ => ℝ) _ (momentVec ν) (momentVec ν')
    simpa [Real.dist_eq, momentVec, f] using this
  rw [← hf.sum_add_tsum_nat_add I]
  have hg : Summable fun i : ℕ => (2⁻¹ : ℝ) ^ (i + I) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right
      ((2⁻¹ : ℝ) ^ I)
    simpa [pow_add] using this
  refine add_le_add (Finset.sum_le_sum fun i _ => min_le_right _ _) ?_
  calc ∑' i, f (i + I) ≤ ∑' i : ℕ, (2⁻¹ : ℝ) ^ (i + I) :=
        Summable.tsum_le_tsum (fun i => min_le_left _ _) ((summable_nat_add_iff I).2 hf) hg
    _ = 2 * 2⁻¹ ^ I := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_inv_two]

/-- The sup metric on `Fin k → FM[0,1]` built from `momentMetric`. -/
theorem dist_pi_le_moments {k : ℕ} (x y : Fin k → St) (I : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ l, ∑ i ∈ Finset.range I, |moment i (x l) - moment i (y l)| ≤ r) :
    @dist (Fin k → St) (@pseudoMetricSpacePi (Fin k) (fun _ => St) _ fun _ => momentMetric).toDist
      x y ≤ r + 2 * 2⁻¹ ^ I := by
  let _ := momentMetric
  refine (dist_pi_le_iff (by positivity)).2 fun l => ?_
  exact (dist_le_moments (x l) (y l) I).trans (add_le_add_left (h l) _)

/-- **The comparison bound** for Lipschitz tests. -/
theorem abs_integral_sub_le {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y Y' : Ω → E} (hY : AEMeasurable Y P)
    (hY' : AEMeasurable Y' P) {f : E → ℝ} {K : ℝ≥0} (hK : LipschitzWith K f) {C : ℝ}
    (hC : ∀ x y, dist (f x) (f y) ≤ C) {B : Set Ω} {r : ℝ} (hr : 0 ≤ r)
    (hB : ∀ ω, ω ∉ B → dist (Y ω) (Y' ω) ≤ r) :
    |∫ ω, f (Y ω) ∂P - ∫ ω, f (Y' ω) ∂P| ≤ K * r + C * (P B).toReal := by
  have := nonempty_of_isProbabilityMeasure P
  have hC0 : 0 ≤ C := le_trans dist_nonneg (hC (Y' Classical.ofNonempty) (Y' Classical.ofNonempty))
  have hint : ∀ {Z : Ω → E}, AEMeasurable Z P → Integrable (fun ω => f (Z ω)) P := by
    intro Z hZ
    refine Integrable.of_bound (hK.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
      (|f (Y' Classical.ofNonempty)| + C) (Eventually.of_forall fun ω => ?_)
    have := hC (Z ω) (Y' Classical.ofNonempty)
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (f (Z ω)) (f (Y' Classical.ofNonempty))
    linarith
  set B' := toMeasurable P B
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable P B
  have hg : Integrable (fun ω => (K : ℝ) * r + B'.indicator (fun _ => C) ω) P :=
    (integrable_const _).add ((integrable_const C).indicator hB'm)
  rw [← integral_sub (hint hY) (hint hY')]
  refine (abs_integral_le_integral_abs).trans ((integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) hg (Eventually.of_forall fun ω => ?_)).trans ?_)
  · dsimp only
    by_cases hω : ω ∈ B'
    · rw [indicator_of_mem hω]
      have := hC (Y ω) (Y' ω)
      rw [Real.dist_eq] at this
      have : 0 ≤ (K : ℝ) * r := by positivity
      linarith
    · rw [indicator_of_notMem hω, add_zero]
      have := hK.dist_le_mul (Y ω) (Y' ω)
      rw [Real.dist_eq] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hB ω fun h => hω (subset_toMeasurable P B h))
        K.coe_nonneg)
  · rw [integral_add (integrable_const _) ((integrable_const C).indicator hB'm),
      integral_const, integral_indicator hB'm, integral_const]
    simp [B', measureReal_def, mul_comm]

end BlockBand.Transmission.LawDuality.SubLimit
