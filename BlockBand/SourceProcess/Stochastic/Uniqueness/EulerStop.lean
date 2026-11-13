module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerLimit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler scheme stopped at a raw stopping time

* `continuous_eulerX`: for a continuous path `w` the interpolated scheme is continuous
  (locally it equals the telescoping sum `eulerX_eq_sum`).
* **`vecCont_predInd_stopSet`** (vector stopping identity, general integrator): a.s. for all
  `v`, `∫_0^v 1_{[[0,τ]]} G dZ = (∫_0^· G dZ)_{v ∧ τ}`.
* **`eulX_rep_stop`**: for an integer horizon `n` and a raw stopping time `τ`, a.s. for all
  `t ≤ n`, `X_{t∧τ} = ξ + ∫_{(0,t]} 1{r ≤ τ} b(E_{j(r)}) dr + ∫_0^t 1_{[[0,τ]]} σ(E_{j(r)}) dB`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ}

theorem continuous_eulerInc (c : LipCoef d) (m : ℕ) (x : Fin d → ℝ) {w : ℝ≥0 → Fin d → ℝ}
    (hw : Continuous w) (j : ℕ) : Continuous (eulerInc c m x w j) := by
  unfold eulerInc
  have h1 : Continuous fun t : ℝ≥0 => min (gridT m (j + 1)) t := continuous_const.min continuous_id
  have h2 : Continuous fun t : ℝ≥0 => min (gridT m j) t := continuous_const.min continuous_id
  exact ((NNReal.continuous_coe.comp h1).sub (NNReal.continuous_coe.comp h2)).smul
    continuous_const |>.add (continuous_const.matrix_mulVec ((hw.comp h1).sub (hw.comp h2)))

theorem continuous_eulerX (c : LipCoef d) (m : ℕ) (x : Fin d → ℝ) {w : ℝ≥0 → Fin d → ℝ}
    (hw : Continuous w) : Continuous (eulerX c m x w) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set J := gridIdx m t₀ + 2
  have hlt : t₀ < gridT m J := (le_gridT_idx_succ m t₀).trans_lt (by
    unfold gridT J; gcongr; exact_mod_cast Nat.lt_succ_self _)
  have hc : Continuous fun t => x + ∑ j ∈ Finset.range J, eulerInc c m x w j t :=
    continuous_const.add (continuous_finsetSum _ fun j _ => continuous_eulerInc c m x hw j)
  refine hc.continuousAt.congr ?_
  filter_upwards [Iio_mem_nhds hlt] with t ht
  exact (eulerX_eq_sum c m x w J (le_of_lt ht)).symm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Vector stopping identity.** -/
theorem vecCont_predInd_stopSet {Q : Measure Ω} [IsFiniteMeasure Q] {ι : Type*} [Fintype ι]
    {Z : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓕 Z a)
    (T : ℝ≥0) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    (G : ι → PredL2 𝓕 (barMeasure Q a T)) :
    ∀ᵐ ω ∂Q, ∀ v, h.vecCont T (fun i => predInd 𝓕 (stopSet τ) (measurableSet_stopSet 𝓕 hτ)
      (G i)) v ω = h.vecCont T G (stopTime (τ ω) v) ω := by
  have hi (i : ι) := (h.coord i).contIntegral_predInd_stopSet_all T (h.restr T i (G i)) hτ
  filter_upwards [ae_all_iff.2 hi] with ω hω v
  simp only [IsL2IntegratorVec.vecCont]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [restr_predInd, hω i v]
  rfl

variable {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ}
  {ξ : Ω → Fin d → ℝ}

theorem continuous_setIntegral_Ioc_comp {f : ℝ → ℝ} {M : ℝ} (hf : Measurable f)
    (hfb : ∀ r, |f r| ≤ M) (n : ℝ≥0) :
    Continuous fun s : ℝ≥0 => ∫ r in Ioc (0 : ℝ) (min s n : ℝ≥0), f r := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    (Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hfb r)).intervalIntegrable
  have h := intervalIntegral.continuous_primitive hii 0
  have e : (fun s : ℝ≥0 => ∫ r in Ioc (0 : ℝ) (min s n : ℝ≥0), f r) =
      fun s : ℝ≥0 => ∫ r in (0 : ℝ)..((min s n : ℝ≥0) : ℝ), f r := funext fun s => by
    rw [intervalIntegral.integral_of_le (min s n).coe_nonneg]
  rw [e]
  exact h.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

/-- **The Euler representation, a.s. for all times `t ≤ n`.** -/
theorem eulX_rep_all (c : LipCoef d) (m : ℕ) (hB : IsFiltrationBrownian P 𝓕 B)
    (hξ : Measurable[𝓕 0] ξ) (n : ℕ) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, eulX c m ξ B t ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, eulDrift c m ξ B (n * 2 ^ m) i (r, ω)) +
        hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (isBddPred_eulDiff c m
          (fun t => (hB.adapted t).measurable) hξ (n * 2 ^ m) i l)) t ω) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => (hB.adapted t).measurable
  have hi : ∀ i, ∀ᵐ ω ∂P, ∀ s : ℝ≥0, eulX c m ξ B (min s n) ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) (min s n : ℝ≥0), eulDrift c m ξ B (n * 2 ^ m) i (r, ω)) +
        hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (isBddPred_eulDiff c m
          hBm hξ (n * 2 ^ m) i l)) (min s n) ω) := fun i => by
    refine ae_forall_eq_of_continuous (X := fun s ω => eulX c m ξ B (min s n) ω i) ?_ ?_
      fun s => eulX_rep c m hB hξ n (min s n) (min_le_right _ _) i
    · filter_upwards [hB.continuous] with ω hω
      exact (continuous_apply i).comp ((continuous_eulerX c m (ξ ω) hω).comp
        (continuous_id.min continuous_const))
    · filter_upwards [(hB.isL2IntegratorVec.vecCont_spec (n : ℝ≥0) fun l => bpL2 _
        (isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l)).1] with ω hω
      exact continuous_const.add ((continuous_setIntegral_Ioc_comp
        ((measurable_eulDrift c m hBm hξ _ i).comp (measurable_id.prodMk measurable_const))
        (fun r => abs_eulDrift_le c m _ i _) n).add
          (hω.comp (continuous_id.min continuous_const)))
  filter_upwards [ae_all_iff.2 hi] with ω hω t ht i
  have := hω i t
  rwa [min_eq_left ht] at this

omit mΩ in
theorem mem_stopSet_iff_le_stopTime {τ : Ω → WithTop ℝ≥0} {r : ℝ} {ω : Ω} {t : ℝ≥0}
    (hr : r ∈ Ioc (0 : ℝ) t) : (r, ω) ∈ stopSet τ ↔ r ≤ stopTime (τ ω) t := by
  rw [mem_stopSet]
  have hc := coe_untopA_min t (τ ω)
  show ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ↔
    r ≤ (((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0) : ℝ)
  have key : r.toNNReal ≤ (min (t : WithTop ℝ≥0) (τ ω)).untopA ↔
      ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (τ ω) := by
    conv_rhs => rw [← hc]
    exact WithTop.coe_le_coe.symm
  rw [← Real.toNNReal_le_iff_le_coe, key, le_min_iff]
  have : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ t := by
    rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]; exact hr.2
  exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩

/-- **The stopped Euler representation.** -/
theorem eulX_rep_stop (c : LipCoef d) (m : ℕ) (hB : IsFiltrationBrownian P 𝓕 B)
    (hξ : Measurable[𝓕 0] ξ) (n : ℕ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, eulX c m ξ B (stopTime (τ ω) t) ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
          (eulDrift c m ξ B (n * 2 ^ m) i) (r, ω)) +
        hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ ((isBddPred_eulDiff c m
          (fun t => (hB.adapted t).measurable) hξ (n * 2 ^ m) i l).indicator
            (measurableSet_stopSet 𝓕 hτ))) t ω) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => (hB.adapted t).measurable
  set μ := barMeasure P (idDens d Ω) (n : ℝ≥0)
  have hst : ∀ i, ∀ᵐ ω ∂P, ∀ v, hB.isL2IntegratorVec.vecCont (n : ℝ≥0)
      (fun l => predInd 𝓕 (stopSet τ) (measurableSet_stopSet 𝓕 hτ)
        (bpL2 μ (isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l))) v ω =
      hB.isL2IntegratorVec.vecCont (n : ℝ≥0)
        (fun l => bpL2 μ (isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l))
        (stopTime (τ ω) v) ω := fun i =>
    vecCont_predInd_stopSet hB.isL2IntegratorVec (n : ℝ≥0) hτ _
  filter_upwards [eulX_rep_all c m hB hξ n, ae_all_iff.2 hst] with ω h1 h2 t ht i
  have hs : stopTime (τ ω) t ≤ t := stopTime_le _ _
  rw [h1 _ (hs.trans ht) i]
  have e1 : (fun l => bpL2 μ ((isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l).indicator
      (measurableSet_stopSet 𝓕 hτ))) = fun l => predInd 𝓕 (stopSet τ)
        (measurableSet_stopSet 𝓕 hτ) (bpL2 μ (isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l)) :=
    funext fun l => bpL2_indicator _ _
  rw [e1, h2 i t]
  congr 2
  have e2 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator (eulDrift c m ξ B (n * 2 ^ m) i) (r, ω) =
      ∫ r in Ioc (0 : ℝ) t, (Iic (stopTime (τ ω) t : ℝ)).indicator
        (fun r => eulDrift c m ξ B (n * 2 ^ m) i (r, ω)) r := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    by_cases h : r ≤ stopTime (τ ω) t
    · rw [indicator_of_mem ((mem_stopSet_iff_le_stopTime hr).2 h),
        indicator_of_mem (show r ∈ Iic (stopTime (τ ω) t : ℝ) from h)]
    · rw [indicator_of_notMem (fun h' => h ((mem_stopSet_iff_le_stopTime hr).1 h')),
        indicator_of_notMem (show r ∉ Iic (stopTime (τ ω) t : ℝ) from h)]
  rw [e2, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
    min_eq_right (NNReal.coe_le_coe.2 hs)]

end BlockBand.SourceProcess.Stochastic.Uniqueness
