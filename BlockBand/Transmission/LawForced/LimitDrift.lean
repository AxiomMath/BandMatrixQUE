module

public import BlockBand.Transmission.LawForced.LimitTest

/-!
# The tested drift sums converge to the limit drift integral

The proof follows `limit_drift_martingale`, but every term is bounded: the drift at a fixed
chamber point is bounded uniformly in `ν` (`exists_bound_ratioDrift`).
* `sum_eq_integral_floor`: the tested sum is `∫_{r₀/W}^{r₁/W} c(⌊Wv⌋) dv`
  (`sum_div_eq_integral`), `c(r) = E[testAt · ratioDriftAt_r]`, `|c| ≤ ‖Φ‖C`;
* `tendsto_c_floor`: for `v > 0`, `c(⌊W_nv⌋) → E[Φ(μ(u_l)) ratioDrift(v, z, μ_v)]`, from
  `tendsto_test_mul` and `ratioDrift(⌊Wv⌋/W) - ratioDrift(v) = (h(v) - h(⌊Wv⌋/W))RF`
  (`ratioDrift_sub_time`), `⌊Wv⌋/W → v`, `h` continuous;
* dominated convergence on `[s, t]` and two boundary cells of length `≤ 1/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal BoundedContinuousFunction

theorem ratioDrift_sub_time (D0 E : ℝ) (κ : ℝ → ℝ) (u u' : ℝ) {p : ℕ} (z : DualCoord p)
    (ν : FiniteMeasure unitInterval) :
    ratioDrift D0 E κ u' z ν - ratioDrift D0 E κ u z ν =
      (absorptionRate E κ u - absorptionRate E κ u') * (∑ i, (z.1 i + z.2 i)) *
        transmissionRatio z.1 z.2 ν := by
  unfold ratioDrift; ring

theorem tendsto_floor_div {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun n => (⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ)) atTop (𝓝 v) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hv).comp
    (tendsto_natCast_atTop_atTop.comp hφ)
  refine h.congr fun n => ?_
  simp only [Function.comp, mul_comm v]

/-- `c(r) = E[testAt · ratioDriftAt_r]`. -/
def testDrift (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) {m : ℕ} (u : Fin m → ℝ)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) {p : ℕ}
    (z : DualCoord p) (r : ℕ) : ℝ :=
  ∫ ω, testAt b E κ W u Φ ω * ratioDriftAt b E κ W r z ω ∂growthPathLaw W b

section

variable {b E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) (hb : b < 1) (hE1 : -2 < E)
  (hE2 : E < 2) {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) {m : ℕ} {u : Fin m → ℝ}
  (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ)

include hκ hb hE1 hE2 hz in
theorem integrable_test_drift (W r : ℕ) :
    Integrable (fun ω => testAt b E κ W u Φ ω * (ratioDriftAt b E κ W r z ω / W))
      (growthPathLaw W b) :=
  (integrable_ratioDriftAt hκ hb hE1 hE2 hz r).bdd_mul
    (Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun l =>
      measurable_stateAt' b E κ _)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_testAt_le b E κ u Φ ω)

include hκ hz in
theorem abs_testDrift_le (W r : ℕ) :
    |testDrift b E κ W u Φ z r| ≤ ‖Φ‖ * (exists_bound_drift (transportD0 b E) E hκ hz).choose := by
  have hC := (exists_bound_drift (transportD0 b E) E hκ hz).choose_spec.2
  have h := norm_integral_le_of_norm_le_const (μ := growthPathLaw W b)
    (f := fun ω => testAt b E κ W u Φ ω * ratioDriftAt b E κ W r z ω)
    (C := ‖Φ‖ * (exists_bound_drift (transportD0 b E) E hκ hz).choose)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_testAt_le b E κ u Φ ω) (hC _ _) (abs_nonneg _) (norm_nonneg _))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

include hκ hb hE1 hE2 hz in
/-- The tested drift sum as a piecewise-constant integral. -/
theorem sum_eq_integral_floor {W : ℕ} (hW : 0 < W) {r₀ r₁ : ℕ} (hr : r₀ ≤ r₁) :
    ∫ ω, testAt b E κ W u Φ ω * ∑ r ∈ Finset.Ico r₀ r₁, ratioDriftAt b E κ W r z ω / W
        ∂growthPathLaw W b =
      ∫ v in (r₀ : ℝ) / W..(r₁ : ℝ) / W, testDrift b E κ W u Φ z ⌊(W : ℝ) * v⌋₊ := by
  rw [← Generator.sum_div_eq_integral hW _ hr]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun r _ => integrable_test_drift hκ hb hE1 hE2 hz Φ W r]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [testDrift, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only; ring

variable {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  (h : IsTransmissionSubLimit b E κ φ P μ) (hu : ∀ l, 0 < u l)

include hκ hb hE1 hE2 hz hφ h hu in
/-- **Pointwise limit of the floor-sampled tested drift.** -/
theorem tendsto_c_floor {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n => testDrift b E κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊) atTop
      (𝓝 (∫ ω, Φ (fun l => μ (u l) ω) * ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
  have hlim := tendsto_test_mul hκ.2.1 hb hE1 hE2 h hu Φ hv (driftBCF (transportD0 b E) E hκ hz v)
  simp only [driftBCF_apply] at hlim
  set R := ∑ i, (z.1 i + z.2 i)
  set hR : ℝ → ℝ := absorptionRate E κ
  have hhc : Continuous hR := by
    unfold hR absorptionRate; exact continuous_const.mul hκ.1
  have hgap : Tendsto (fun n => ‖Φ‖ * |R| *
      |hR v - hR ((⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ))|) atTop (𝓝 0) := by
    have h1 := (hhc.tendsto v).comp (tendsto_floor_div hφ hv.le)
    have h2 : Tendsto (fun n => |hR v - hR ((⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ))|) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := hR v)).sub h1
      simpa using this.abs
    simpa using h2.const_mul (‖Φ‖ * |R|)
  set C := (exists_bound_drift (transportD0 b E) E hκ hz).choose
  have hC := (exists_bound_drift (transportD0 b E) E hκ hz).choose_spec.2
  have htest : ∀ n, Measurable (testAt b E κ (φ n) u Φ) := fun n =>
    Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun l => measurable_stateAt' b E κ _)
  have hdiff : ∀ n, ‖testDrift b E κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊ -
      ∫ ω, testAt b E κ (φ n) u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b E κ (φ n) v ω)
          ∂growthPathLaw (φ n) b‖ ≤
      ‖Φ‖ * |R| * |hR v - hR ((⌊((φ n : ℕ) : ℝ) * v⌋₊ : ℝ) / (φ n : ℝ))| := by
    intro n
    set W := φ n
    have hTP := aemeasurable_transmissionProcess (W := W) hκ.2.1 hb hE1 hE2 v
    have hA : Integrable (fun ω => testAt b E κ W u Φ ω *
        ratioDriftAt b E κ W ⌊(W : ℝ) * v⌋₊ z ω) (growthPathLaw W b) := by
      refine Integrable.of_bound (C := ‖Φ‖ * C) ((htest n).aestronglyMeasurable.mul ?_)
        (Eventually.of_forall fun ω => ?_)
      · exact ((continuous_ratioDrift_nu _ E hκ.1 hz _).measurable.comp_aemeasurable
          hTP).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_testAt_le b E κ u Φ ω) (hC _ _) (abs_nonneg _) (norm_nonneg _)
    have hB : Integrable (fun ω => testAt b E κ W u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b E κ W v ω))
        (growthPathLaw W b) := by
      refine Integrable.of_bound (C := ‖Φ‖ * C) ((htest n).aestronglyMeasurable.mul ?_)
        (Eventually.of_forall fun ω => ?_)
      · exact ((continuous_ratioDrift_nu _ E hκ.1 hz _).measurable.comp_aemeasurable
          hTP).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_testAt_le b E κ u Φ ω) (hC _ _) (abs_nonneg _) (norm_nonneg _)
    rw [testDrift, ← integral_sub hA hB]
    have h := norm_integral_le_of_norm_le_const (μ := growthPathLaw W b)
      (f := fun ω => testAt b E κ W u Φ ω * ratioDriftAt b E κ W ⌊(W : ℝ) * v⌋₊ z ω -
        testAt b E κ W u Φ ω *
          ratioDrift (transportD0 b E) E κ v z (transmissionProcess b E κ W v ω))
      (C := ‖Φ‖ * |R| * |hR v - hR ((⌊(W : ℝ) * v⌋₊ : ℝ) / (W : ℝ))|)
      (Eventually.of_forall fun ω => by
        rw [← mul_sub, ratioDriftAt]
        have e := ratioDrift_sub_time (transportD0 b E) E κ v ((⌊(W : ℝ) * v⌋₊ : ℝ) / W) z
          (traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * v⌋₊ ω))
        have hF := transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz)
          (traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * v⌋₊ ω))
        change ‖testAt b E κ W u Φ ω * (ratioDrift (transportD0 b E) E κ
          ((⌊(W : ℝ) * v⌋₊ : ℝ) / W) z (traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * v⌋₊ ω)) -
          ratioDrift (transportD0 b E) E κ v z
            (traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * v⌋₊ ω)))‖ ≤ _
        rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hF.1]
        have h1 := abs_testAt_le b E κ u Φ ω
        calc |testAt b E κ W u Φ ω| * (|hR v - hR ((⌊(W : ℝ) * v⌋₊ : ℝ) / W)| * |R| *
              transmissionRatio z.1 z.2
                (traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * v⌋₊ ω)))
            ≤ ‖Φ‖ * (|hR v - hR ((⌊(W : ℝ) * v⌋₊ : ℝ) / W)| * |R| * 1) := by
              gcongr
              · exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hF.1.le
              · exact hF.2
          _ = _ := by ring)
    rwa [probReal_univ, mul_one] at h
  have h0 : Tendsto (fun n => testDrift b E κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊ -
      ∫ ω, testAt b E κ (φ n) u Φ ω *
        ratioDrift (transportD0 b E) E κ v z (transmissionProcess b E κ (φ n) v ω)
          ∂growthPathLaw (φ n) b) atTop (𝓝 0) := squeeze_zero_norm hdiff hgap
  simpa using h0.add hlim

include hκ hb hE1 hE2 hz hφ h hu in
/-- **The tested drift sums converge to the limit drift integral.** -/
theorem tendsto_drift_sum {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    Tendsto (fun n => ∫ ω, testAt b E κ (φ n) u Φ ω *
        ∑ r ∈ Finset.Ico ⌊((φ n : ℕ) : ℝ) * s⌋₊ ⌊((φ n : ℕ) : ℝ) * t⌋₊,
          ratioDriftAt b E κ (φ n) r z ω / (φ n : ℝ) ∂growthPathLaw (φ n) b) atTop
      (𝓝 (∫ v in s..t, ∫ ω, Φ (fun l => μ (u l) ω) *
        ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
  set K := ‖Φ‖ * (exists_bound_drift (transportD0 b E) E hκ hz).choose
  set g : ℕ → ℝ → ℝ := fun n v => testDrift b E κ (φ n) u Φ z ⌊((φ n : ℕ) : ℝ) * v⌋₊
  have hgK : ∀ n v, ‖g n v‖ ≤ K := fun n v => by
    rw [Real.norm_eq_abs]; exact abs_testDrift_le hκ hz Φ _ _
  have hgi : ∀ n x y, IntervalIntegrable (g n) volume x y := fun n x y =>
    Generator.intervalIntegrable_floor_comp (W := φ n) (testDrift b E κ (φ n) u Φ z) x y
  -- the middle integral
  have hmid : Tendsto (fun n => ∫ v in s..t, g n v) atTop
      (𝓝 (∫ v in s..t, ∫ ω, Φ (fun l => μ (u l) ω) *
        ratioDrift (transportD0 b E) E κ v z (μ v ω) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
      (Eventually.of_forall fun n => (hgi n s t).def'.aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun v _ => hgK n v)
      intervalIntegrable_const (Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := by
      rw [Set.uIoc_of_le hst] at hv; exact hs.trans hv.1
    exact tendsto_c_floor hκ hb hE1 hE2 hz Φ hφ h hu hv0
  -- the boundary cells
  have hcell : ∀ {x : ℝ}, 0 < x → Tendsto (fun n =>
      ∫ v in (⌊((φ n : ℕ) : ℝ) * x⌋₊ : ℝ) / (φ n : ℝ)..x, g n v) atTop (𝓝 0) := by
    intro x hx
    have hcon := tendsto_floor_div hφ hx.le
    have hb0 : Tendsto (fun n => K * |x - (⌊((φ n : ℕ) : ℝ) * x⌋₊ : ℝ) / (φ n : ℝ)|) atTop
        (𝓝 0) := by
      have := ((tendsto_const_nhds (x := x)).sub hcon).abs.const_mul K
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hb0
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun v _ => hgK n v
  have hlim := ((hcell hs).add hmid).sub (hcell (hs.trans_le hst))
  simp only [zero_add, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hφ.eventually_ge_atTop 1] with n hn
  have hW : 0 < φ n := hn
  have hr : ⌊((φ n : ℕ) : ℝ) * s⌋₊ ≤ ⌊((φ n : ℕ) : ℝ) * t⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))
  rw [sum_eq_integral_floor hκ hb hE1 hE2 hz Φ hW hr]
  change _ = ∫ v in (⌊((φ n : ℕ) : ℝ) * s⌋₊ : ℝ) / (φ n : ℝ)..(⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) /
    (φ n : ℝ), g n v
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hgi n ((⌊((φ n : ℕ) : ℝ) * s⌋₊ : ℝ) / (φ n : ℝ)) s)
    (hgi n s ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ)))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hgi n s t)
    (hgi n t ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ)))
  have e3 := intervalIntegral.integral_symm (f := g n) (μ := volume) t
    ((⌊((φ n : ℕ) : ℝ) * t⌋₊ : ℝ) / (φ n : ℝ))
  linarith

end

end BlockBand.Transmission.LawForced
