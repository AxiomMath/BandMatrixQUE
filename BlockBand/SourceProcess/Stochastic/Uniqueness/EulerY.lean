module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerStop
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Euler scheme versus a stopped solution: the pathwise-uniqueness estimate

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion,
`ξ` `𝓕_0`-measurable, `c : LipCoef d`, a raw stopping time `τ`, an integer horizon `n`, and a
process `Y` (measurable marginals, a.s. continuous) satisfying, a.s. for all `t ≤ n`,
`Y_{t∧τ} = ξ + ∫_{(0,t]} 1{r ≤ τ} b(Y_r) dr + ∫_0^t γ^Y dB` with a bounded predictable `γ^Y`
equal a.s. on `(0, n]` to `1{r ≤ τ} σ(Y_r)`.

**`lintegral_eulX_stop_sub_le`**: for `t ≤ n`,
`E |X^m_{t∧τ} - Y_{t∧τ}|² ≤ gronC(n, eulLip c) · δ_c 2^{-m}` (squared Euclidean norm).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

/-- The stopped time `r⁺ ∧ τ` as a real number. -/
def stopR (τ : Ω → WithTop ℝ≥0) (p : ℝ × Ω) : ℝ := (stopTime (τ p.2) p.1.toNNReal : ℝ)

theorem measurable_stopR {τ : Ω → WithTop ℝ≥0} (hτ : Measurable τ) :
    Measurable fun p : ℝ × Ω => (stopR τ p, p.2) := by
  refine Measurable.prodMk ?_ measurable_snd
  exact (Measurable.untopA (((measurable_real_toNNReal.comp measurable_fst).withTop_coe).min
    (hτ.comp measurable_snd))).coe_nnreal_real

omit mΩ in
theorem stopR_of_mem {τ : Ω → WithTop ℝ≥0} {r : ℝ} {ω : Ω} (hr : 0 < r)
    (h : (r, ω) ∈ stopSet τ) : stopR τ (r, ω) = r := by
  simp only [stopR]
  rw [stopTime_of_le h, Real.coe_toNNReal _ hr.le]

variable {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ}
  {ξ : Ω → Fin d → ℝ}

/-- **The Euler scheme approximates a stopped solution.** -/
theorem lintegral_eulX_stop_sub_le (hB : IsFiltrationBrownian P 𝓕 B) (c : LipCoef d)
    (hξ : Measurable[𝓕 0] ξ) (n m : ℕ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ᵐ ω ∂P, Continuous fun t => Y t ω)
    {γY : Fin d → Fin d → ℝ × Ω → ℝ} (hγY : ∀ i l, IsBddPred 𝓕 (γY i l))
    (hγYe : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) n, ∀ i l, γY i l (r, ω) =
      (stopSet τ).indicator (fun p => c.σ (Y p.1.toNNReal p.2) i l) (r, ω))
    (hrep : haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
      ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, Y (stopTime (τ ω) t) ω i = ξ ω i +
        ((∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
            (fun p => c.b (Y p.1.toNNReal p.2) i) (r, ω)) +
          hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (hγY i l)) t ω)) :
    ∀ t ≤ (n : ℝ≥0), ∫⁻ ω, ∑ i, ‖eulX c m ξ B (stopTime (τ ω) t) ω i -
      Y (stopTime (τ ω) t) ω i‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (gronC n (eulLip c)) * ENNReal.ofReal (eulDelta c / 2 ^ m) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => (hB.adapted t).measurable
  have hBm' : ∀ t, Measurable (B t) := fun t => (hBm t).mono (𝓕.le t) le_rfl
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set hB.continuous
  obtain ⟨A', hA', hAP', hAc'⟩ := exists_good_set hYc
  have hE : ∀ j, Measurable (eulE c m ξ B j) := fun j =>
    (measurable_eulE c m hBm hξ j).mono (𝓕.le _) le_rfl
  have hτm : Measurable τ := hτ.measurable'
  set Yv := jointVersion Y A'
  have hYv : Measurable Yv := measurable_jointVersion hYm hA' hAc'
  have hS := measurableSet_stopSet 𝓕 hτ
  have hSm : MeasurableSet (stopSet τ) := predictableSpace_le _ _ hS
  set J := n * 2 ^ m
  have hn : gridT m J = n := gridT_mul_pow m n
  set β : Fin d → ℝ × Ω → ℝ := fun i p => (stopSet τ).indicator (eulDrift c m ξ B J i) p -
    (stopSet τ).indicator (fun q => c.b (Yv q) i) p
  have hβ : ∀ i, Measurable (β i) := fun i =>
    ((measurable_eulDrift c m hBm hξ J i).indicator hSm).sub
      ((((measurable_pi_apply i).comp c.continuous_b.measurable).comp hYv).indicator hSm)
  have hβb : ∀ i p, |β i p| ≤ 2 * c.M := fun i p => by
    have a1 : |(stopSet τ).indicator (eulDrift c m ξ B J i) p| ≤ c.M := by
      classical
      rw [indicator_apply]; split_ifs
      · exact abs_eulDrift_le c m J i p
      · simp [c.M_nonneg]
    have a2 : |(stopSet τ).indicator (fun q => c.b (Yv q) i) p| ≤ c.M := by
      classical
      rw [indicator_apply]; split_ifs
      · exact c.bd_b _ _
      · simp [c.M_nonneg]
    exact (abs_sub _ _).trans (by linarith)
  have h1 := fun i l => (isBddPred_eulDiff c m hBm hξ J i l).indicator hS
  have hγ : ∀ i l, IsBddPred 𝓕 fun p =>
      (stopSet τ).indicator (eulDiff c m ξ B J i l) p - γY i l p :=
    fun i l => isBddPred_sub (h1 i l) (hγY i l)
  set D' : ℝ × Ω → Fin d → ℝ := fun p =>
    eulXv c m ξ B A (stopR τ p, p.2) - Yv (stopR τ p, p.2)
  have hD' : Measurable D' :=
    ((measurable_eulXv c m hBm' hE hA hAc).comp (measurable_stopR hτm)).sub
      (hYv.comp (measurable_stopR hτm))
  have hAA : ∀ᵐ ω ∂P, ω ∈ A ∧ ω ∈ A' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP,
      measure_eq_zero_iff_ae_notMem.1 hAP'] with ω h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  have hDD : ∀ s : ℝ≥0, s ≤ (n : ℝ≥0) → ∀ᵐ ω ∂P,
      (fun i => eulX c m ξ B (stopTime (τ ω) s) ω i - Y (stopTime (τ ω) s) ω i) =
        D' ((s : ℝ), ω) := by
    intro s _
    filter_upwards [hAA] with ω hω
    simp only [D', eulXv_of_mem c m hω.1, jointVersion_of_mem hω.2, stopR, Real.toNNReal_coe,
      Yv]
    rfl
  set ε : ℝ × Ω → ℝ≥0∞ := eulEps c m ξ B A
  have hε : Measurable ε := measurable_eulEps c m hBm' hE hA hAc
  refine lintegral_sq_le_gronwall hB (D := fun s ω i => eulX c m ξ B (stopTime (τ ω) s) ω i -
    Y (stopTime (τ ω) s) ω i) hD' hDD hβ hβb hγ ?_ hε ENNReal.ofReal_ne_top
    (fun r hr => lintegral_eulEps_le hB c m hAP hr.1.le) ?_
  · -- the representation
    intro t ht i
    have e : (fun l => bpL2 (barMeasure P (idDens d Ω) n) (hγ i l)) =
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (h1 i l)) -
          fun l => bpL2 (barMeasure P (idDens d Ω) n) (hγY i l) :=
      funext fun l => bpL2_sub' (h1 i l) (hγY i l)
    filter_upwards [eulX_rep_stop c m hB hξ n hτ, hrep, hAA,
      vecCont_sub_ae hB.isL2IntegratorVec (n : ℝ≥0)
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (h1 i l))
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (hγY i l)) t] with ω e1 e2 hω e3
    rw [e1 t ht i, e2 t ht i, e, e3]
    have hi1 : IntegrableOn (fun r => (stopSet τ).indicator (eulDrift c m ξ B J i) (r, ω))
        (Ioc (0 : ℝ) t) :=
      Measure.integrableOn_of_bounded (M := c.M) (by simp)
        (((measurable_eulDrift c m hBm hξ J i).indicator hSm).comp (measurable_id.prodMk
          measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          classical
          rw [Real.norm_eq_abs, indicator_apply]; split_ifs
          · exact abs_eulDrift_le c m J i _
          · simp [c.M_nonneg])
    have hi2 : IntegrableOn (fun r => (stopSet τ).indicator (fun q => c.b (Yv q) i) (r, ω))
        (Ioc (0 : ℝ) t) :=
      Measure.integrableOn_of_bounded (M := c.M) (by simp)
        (((((measurable_pi_apply i).comp c.continuous_b.measurable).comp hYv).indicator
          hSm).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          classical
          rw [Real.norm_eq_abs, indicator_apply]; split_ifs
          · exact c.bd_b _ _
          · simp [c.M_nonneg])
    have e4 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
        (fun p => c.b (Y p.1.toNNReal p.2) i) (r, ω) =
        ∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator (fun q => c.b (Yv q) i) (r, ω) := by
      congr 1
      funext r
      by_cases hr : (r, ω) ∈ stopSet τ
      · rw [indicator_of_mem hr, indicator_of_mem hr]
        exact congrArg (fun y => c.b y i) (jointVersion_of_mem hω.2 r).symm
      · rw [indicator_of_notMem hr, indicator_of_notMem hr]
    simp only [β]
    rw [e4, integral_sub hi1 hi2]
    ring
  · -- the pointwise bound
    filter_upwards [hAA, hγYe] with ω hω hγω r hr
    have hrn : r ≤ gridT m J := by rw [hn]; exact hr.2
    by_cases hS' : (r, ω) ∈ stopSet τ
    · have eb : ∀ i, β i (r, ω) = c.b (eulE c m ξ B (gridIdx m r.toNNReal) ω) i -
          c.b (Yv (r, ω)) i := fun i => by
        simp only [β, indicator_of_mem hS', eulDrift_eq c m hr.1 hrn]
      have eg : ∀ i l, (stopSet τ).indicator (eulDiff c m ξ B J i l) (r, ω) - γY i l (r, ω) =
          c.σ (eulE c m ξ B (gridIdx m r.toNNReal) ω) i l - c.σ (Yv (r, ω)) i l := fun i l => by
        rw [hγω r hr i l, indicator_of_mem hS', indicator_of_mem hS', eulDiff_eq c m hr.1 hrn]
        simp only [Yv, jointVersion_of_mem hω.2]
      unfold coefSq
      simp only [eb, eg]
      have hD'r : D' (r, ω) = eulXv c m ξ B A (r, ω) - Yv (r, ω) := by
        simp only [D', stopR_of_mem hr.1 hS']
      have hb := coefSq_euler_bound c (eulE c m ξ B (gridIdx m r.toNNReal) ω) (Yv (r, ω))
        (eulXv c m ξ B A (r, ω)) (Yv (r, ω))
      simp only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, add_zero] at hb
      rw [hD'r]
      exact hb
    · have eb : ∀ i, β i (r, ω) = 0 := fun i => by
        simp only [β, indicator_of_notMem hS', sub_self]
      have eg : ∀ i l, (stopSet τ).indicator (eulDiff c m ξ B J i l) (r, ω) - γY i l (r, ω) =
          0 := fun i l => by
        rw [hγω r hr i l, indicator_of_notMem hS', indicator_of_notMem hS', sub_self]
      unfold coefSq
      simp only [eb, eg, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, add_zero]
      exact zero_le

end BlockBand.SourceProcess.Stochastic.Uniqueness
