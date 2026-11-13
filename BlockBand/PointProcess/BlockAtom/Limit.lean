module

public import Mathlib

/-!
# Weak limits of unbounded continuous functionals under a second-moment bound

The generic measure-theoretic step of the vanishing of block atoms. For probability measures
`P j → Q` weakly on a topological space with open sets measurable, and a continuous nonnegative
real functional `Ψ` whose second moments are bounded uniformly in `j`:

* `eventually_lintegral_le_add`: for every `ε > 0`, eventually `E_{P j} Ψ ≤ E_Q Ψ + ε`
  (upper limit; uniform integrability from the second moment);
* `lintegral_le_of_tendsto`: `E_Q Ψ` is bounded by any uniform bound of `E_{P j} Ψ` (lower
  semicontinuity of the expectation of a nonnegative continuous functional).
All expectations are lower integrals of `ENNReal.ofReal Ψ`, so no integrability is assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.PointProcess.BlockAtom

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The truncation `min(Ψ, K)` of a nonnegative continuous functional, as a bounded continuous
`ℝ≥0`-valued function. -/
def truncation (Ψ : X → ℝ) (hΨ : Continuous Ψ) (K : ℝ≥0) : X →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (Real.toNNReal (Ψ x)) K,
      (continuous_real_toNNReal.comp hΨ).min continuous_const⟩ K (by
    intro x y
    simp only [ContinuousMap.coe_mk, NNReal.dist_eq]
    have h1 : ((min (Real.toNNReal (Ψ x)) K : ℝ≥0) : ℝ) ≤ K := by exact_mod_cast min_le_right _ _
    have h2 : ((min (Real.toNNReal (Ψ y)) K : ℝ≥0) : ℝ) ≤ K := by exact_mod_cast min_le_right _ _
    have h3 : (0 : ℝ) ≤ ((min (Real.toNNReal (Ψ x)) K : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have h4 : (0 : ℝ) ≤ ((min (Real.toNNReal (Ψ y)) K : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    rw [abs_le]
    constructor <;> linarith)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem truncation_apply (Ψ : X → ℝ) (hΨ : Continuous Ψ) (K : ℝ≥0) (x : X) :
    truncation Ψ hΨ K x = min (Real.toNNReal (Ψ x)) K := rfl

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- `ofReal Ψ ≤ min(Ψ, K) + (ofReal Ψ)² / K` for `K > 0`. -/
theorem ofReal_le_truncation_add (Ψ : X → ℝ) (hΨ : Continuous Ψ) {K : ℝ≥0} (hK : 0 < K) (x : X) :
    ENNReal.ofReal (Ψ x) ≤ (truncation Ψ hΨ K x : ℝ≥0∞) + ENNReal.ofReal (Ψ x) ^ 2 / K := by
  rw [truncation_apply]
  by_cases hle : Real.toNNReal (Ψ x) ≤ K
  · rw [min_eq_left hle]
    calc ENNReal.ofReal (Ψ x) = ((Real.toNNReal (Ψ x) : ℝ≥0) : ℝ≥0∞) := rfl
      _ ≤ _ := le_self_add
  · rw [not_le] at hle
    rw [min_eq_right hle.le]
    refine le_add_left ?_
    have hKne : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hKne) (Or.inl ENNReal.coe_ne_top), pow_two]
    have : (K : ℝ≥0∞) ≤ ENNReal.ofReal (Ψ x) := by
      change ((K : ℝ≥0) : ℝ≥0∞) ≤ ((Real.toNNReal (Ψ x) : ℝ≥0) : ℝ≥0∞)
      exact_mod_cast hle.le
    gcongr

/-- Weak convergence of the truncated expectations. -/
theorem tendsto_lintegral_truncation {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hPQ : Tendsto P atTop (𝓝 Q)) (Ψ : X → ℝ) (hΨ : Continuous Ψ) (K : ℝ≥0) :
    Tendsto (fun j => ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(P j : Measure X)) atTop
      (𝓝 (∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X))) :=
  (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hPQ) (truncation Ψ hΨ K)

/-- Upper limit under a uniform second-moment bound: eventually
`E_{P j} Ψ ≤ E_Q Ψ + ε`. -/
theorem eventually_lintegral_le_add {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hPQ : Tendsto P atTop (𝓝 Q)) (Ψ : X → ℝ) (hΨ : Continuous Ψ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h2 : ∀ j, ∫⁻ x, ENNReal.ofReal (Ψ x) ^ 2 ∂(P j : Measure X) ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(P j : Measure X) ≤
      ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(Q : Measure X) + ε := by
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun j => by simp [hεt]
  -- choose `K` with `C / K ≤ ε / 2`
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K, hKpos, hK⟩ : ∃ K : ℝ≥0, 0 < K ∧ C / K ≤ ε / 2 := by
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, C = c := ⟨C.toNNReal, (ENNReal.coe_toNNReal hC).symm⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ≥0, ε / 2 = e := ⟨(ε / 2).toNNReal,
      (ENNReal.coe_toNNReal (ENNReal.div_ne_top hεt (by norm_num))).symm⟩
    have he0 : 0 < e := by
      have := hε2; rw [he] at this; exact_mod_cast this
    have hK0 : (0 : ℝ≥0) < c / e + 1 := by positivity
    refine ⟨c / e + 1, hK0, ?_⟩
    rw [hc, he, ENNReal.div_le_iff (by exact_mod_cast hK0.ne') ENNReal.coe_ne_top,
      ← ENNReal.coe_mul]
    have : c ≤ e * (c / e + 1) := by
      rw [mul_add, mul_div_cancel₀ c he0.ne', mul_one]
      exact le_self_add
    exact_mod_cast this
  have hlim := tendsto_lintegral_truncation hPQ Ψ hΨ K
  have htrQ : ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X) ≤
      ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(Q : Measure X) := by
    apply lintegral_mono
    intro x
    simp only [truncation_apply]
    change ((min (Real.toNNReal (Ψ x)) K : ℝ≥0) : ℝ≥0∞) ≤ ((Real.toNNReal (Ψ x) : ℝ≥0) : ℝ≥0∞)
    exact_mod_cast min_le_left _ _
  have hfin : ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := K)) ?_
    calc ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X)
        ≤ ∫⁻ _x, (K : ℝ≥0∞) ∂(Q : Measure X) := by
          apply lintegral_mono
          intro x
          simp only [truncation_apply]
          exact_mod_cast min_le_right _ _
      _ = K := by simp
  have hev : ∀ᶠ j in atTop, ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(P j : Measure X) ≤
      ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X) + ε / 2 :=
    (ENNReal.tendsto_nhds hfin).1 hlim (ε / 2) hε2 |>.mono fun j hj => hj.2
  filter_upwards [hev] with j hj
  calc ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(P j : Measure X)
      ≤ ∫⁻ x, ((truncation Ψ hΨ K x : ℝ≥0∞) + ENNReal.ofReal (Ψ x) ^ 2 / K)
          ∂(P j : Measure X) := lintegral_mono fun x => ofReal_le_truncation_add Ψ hΨ hKpos x
    _ = ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(P j : Measure X) +
          ∫⁻ x, ENNReal.ofReal (Ψ x) ^ 2 / K ∂(P j : Measure X) :=
        lintegral_add_left (ENNReal.continuous_coe.comp (truncation Ψ hΨ K).continuous).measurable _
    _ = ∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(P j : Measure X) +
          (∫⁻ x, ENNReal.ofReal (Ψ x) ^ 2 ∂(P j : Measure X)) / K := by
        congr 1
        simp_rw [div_eq_mul_inv]
        rw [lintegral_mul_const' _ _ (by simp [hKpos.ne'])]
    _ ≤ (∫⁻ x, (truncation Ψ hΨ K x : ℝ≥0∞) ∂(Q : Measure X) + ε / 2) + C / K :=
        add_le_add hj (ENNReal.div_le_div_right (h2 j) _)
    _ ≤ (∫⁻ x, ENNReal.ofReal (Ψ x) ∂(Q : Measure X) + ε / 2) + ε / 2 :=
        add_le_add (add_le_add htrQ le_rfl) hK
    _ = ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(Q : Measure X) + ε := by
        rw [add_assoc, ENNReal.add_halves]

/-- Lower semicontinuity: a uniform bound on `E_{P j} Ψ` bounds `E_Q Ψ`. -/
theorem lintegral_le_of_tendsto {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hPQ : Tendsto P atTop (𝓝 Q)) (Ψ : X → ℝ) (hΨ : Continuous Ψ) (C : ℝ≥0∞)
    (h1 : ∀ j, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(P j : Measure X) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (Ψ x) ∂(Q : Measure X) ≤ C := by
  -- `ofReal Ψ = ⨆ K, min(Ψ, K)`, monotone in `K`
  have hsup : ∀ x, ENNReal.ofReal (Ψ x) = ⨆ K : ℕ, (truncation Ψ hΨ (K : ℝ≥0) x : ℝ≥0∞) := by
    intro x
    apply le_antisymm
    · obtain ⟨K, hK⟩ := exists_nat_ge (Real.toNNReal (Ψ x))
      refine le_iSup_of_le K ?_
      rw [truncation_apply, min_eq_left hK]
      rfl
    · refine iSup_le fun K => ?_
      rw [truncation_apply]
      change ((min (Real.toNNReal (Ψ x)) (K : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
        ((Real.toNNReal (Ψ x) : ℝ≥0) : ℝ≥0∞)
      exact_mod_cast min_le_left _ _
  have hmono : Monotone fun (K : ℕ) x => (truncation Ψ hΨ (K : ℝ≥0) x : ℝ≥0∞) := by
    intro K K' hKK' x
    simp only [truncation_apply]
    have : (K : ℝ≥0) ≤ K' := by exact_mod_cast hKK'
    exact_mod_cast min_le_min_left _ this
  have hmeas : ∀ K : ℕ, Measurable fun x => (truncation Ψ hΨ (K : ℝ≥0) x : ℝ≥0∞) :=
    fun K => (ENNReal.continuous_coe.comp (truncation Ψ hΨ (K : ℝ≥0)).continuous).measurable
  simp_rw [hsup]
  rw [lintegral_iSup hmeas hmono]
  refine iSup_le fun K => ?_
  have hlim := tendsto_lintegral_truncation hPQ Ψ hΨ (K : ℝ≥0)
  refine le_of_tendsto' hlim fun j => ?_
  refine (lintegral_mono fun x => ?_).trans (h1 j)
  rw [truncation_apply]
  change ((min (Real.toNNReal (Ψ x)) (K : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
    ((Real.toNNReal (Ψ x) : ℝ≥0) : ℝ≥0∞)
  exact_mod_cast min_le_left _ _

end BlockBand.PointProcess.BlockAtom
