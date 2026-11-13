module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerCauchy
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Consecutive Euler schemes are `2^{-m}`-close in `L²`

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion, `ξ`
`𝓕_0`-measurable, `c : LipCoef d`, integer horizon `n`.

**`lintegral_eulX_succ_sub_le`**: for `t ≤ n`,
`E |X^{m+1}_t - X^m_t|² ≤ gronC(n, eulLip c) · 2 δ_c 2^{-m}` (squared Euclidean norm).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open scoped NNReal ENNReal

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} {ξ : Ω → Fin d → ℝ}

/-- **Consecutive Euler schemes are close.** -/
theorem lintegral_eulX_succ_sub_le (hB : IsFiltrationBrownian P 𝓕 B) (c : LipCoef d)
    (hξ : Measurable[𝓕 0] ξ) (n m : ℕ) {t : ℝ≥0} (ht : t ≤ n) :
    ∫⁻ ω, ∑ i, ‖eulX c (m + 1) ξ B t ω i - eulX c m ξ B t ω i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (gronC n (eulLip c)) * ENNReal.ofReal (2 * eulDelta c / 2 ^ m) := by
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => (hB.adapted t).measurable
  have hBm' : ∀ t, Measurable (B t) := fun t => (hBm t).mono (𝓕.le t) le_rfl
  obtain ⟨A, hA, hAP, hAc⟩ := exists_good_set hB.continuous
  have hE : ∀ m j, Measurable (eulE c m ξ B j) := fun m j =>
    (measurable_eulE c m hBm hξ j).mono (𝓕.le _) le_rfl
  have hn' : gridT (m + 1) (n * 2 ^ (m + 1)) = n := gridT_mul_pow (m + 1) n
  have hn : gridT m (n * 2 ^ m) = n := gridT_mul_pow m n
  set β : Fin d → ℝ × Ω → ℝ := fun i p =>
    eulDrift c (m + 1) ξ B (n * 2 ^ (m + 1)) i p - eulDrift c m ξ B (n * 2 ^ m) i p
  have hβ : ∀ i, Measurable (β i) := fun i =>
    (measurable_eulDrift c (m + 1) hBm hξ _ i).sub (measurable_eulDrift c m hBm hξ _ i)
  have hβb : ∀ i p, |β i p| ≤ 2 * c.M := fun i p => by
    have a1 := abs_eulDrift_le c (m + 1) (ξ := ξ) (B := B) (n * 2 ^ (m + 1)) i p
    have a2 := abs_eulDrift_le c m (ξ := ξ) (B := B) (n * 2 ^ m) i p
    exact (abs_sub _ _).trans (by linarith)
  have h1 := fun i l => isBddPred_eulDiff c (m + 1) hBm hξ (n * 2 ^ (m + 1)) i l
  have h2 := fun i l => isBddPred_eulDiff c m hBm hξ (n * 2 ^ m) i l
  have hγ : ∀ i l, IsBddPred 𝓕 fun p =>
      eulDiff c (m + 1) ξ B (n * 2 ^ (m + 1)) i l p - eulDiff c m ξ B (n * 2 ^ m) i l p :=
    fun i l => isBddPred_sub (h1 i l) (h2 i l)
  set D' : ℝ × Ω → Fin d → ℝ := fun p => eulXv c (m + 1) ξ B A p - eulXv c m ξ B A p
  have hD' : Measurable D' :=
    (measurable_eulXv c (m + 1) hBm' (hE (m + 1)) hA hAc).sub
      (measurable_eulXv c m hBm' (hE m) hA hAc)
  have hDD : ∀ s : ℝ≥0, s ≤ (n : ℝ≥0) → ∀ᵐ ω ∂P,
      (fun i => eulX c (m + 1) ξ B s ω i - eulX c m ξ B s ω i) = D' ((s : ℝ), ω) := by
    intro s _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω hω
    have hω' : ω ∈ A := by simpa using hω
    simp only [D', eulXv_of_mem c (m + 1) hω', eulXv_of_mem c m hω', Real.toNNReal_coe]
    rfl
  set ε : ℝ × Ω → ℝ≥0∞ := fun p => eulEps c (m + 1) ξ B A p + eulEps c m ξ B A p
  have hε : Measurable ε := (measurable_eulEps c (m + 1) hBm' (hE (m + 1)) hA hAc).add
    (measurable_eulEps c m hBm' (hE m) hA hAc)
  refine lintegral_sq_le_gronwall hB (D := fun s ω i => eulX c (m + 1) ξ B s ω i -
    eulX c m ξ B s ω i) hD' hDD hβ hβb hγ ?_ hε ENNReal.ofReal_ne_top ?_ ?_ t ht
  · -- the representation
    have := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    intro t ht i
    have e : (fun l => bpL2 (barMeasure P (idDens d Ω) n) (hγ i l)) =
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (h1 i l)) -
          fun l => bpL2 (barMeasure P (idDens d Ω) n) (h2 i l) :=
      funext fun l => bpL2_sub' (h1 i l) (h2 i l)
    filter_upwards [eulX_rep c (m + 1) hB hξ n t ht i, eulX_rep c m hB hξ n t ht i,
      vecCont_sub_ae hB.isL2IntegratorVec (n : ℝ≥0)
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (h1 i l))
        (fun l => bpL2 (barMeasure P (idDens d Ω) n) (h2 i l)) t] with ω e1 e2 e3
    rw [e1, e2, e, e3]
    have hi : ∀ (m' J : ℕ), IntegrableOn (fun r => eulDrift c m' ξ B J i (r, ω))
        (Ioc (0 : ℝ) t) := fun m' J =>
      Measure.integrableOn_of_bounded (M := c.M) (by simp)
        ((measurable_eulDrift c m' hBm hξ J i).comp (measurable_id.prodMk
          measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs]; exact abs_eulDrift_le c m' J i _)
    simp only [β]
    rw [integral_sub (hi (m + 1) _) (hi m _)]
    ring
  · -- the discretisation errors
    intro r hr
    have hm1 : Measurable fun ω => eulEps c (m + 1) ξ B A (r, ω) :=
      (measurable_eulEps c (m + 1) hBm' (hE (m + 1)) hA hAc).comp
        (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left' hm1.aemeasurable]
    refine (add_le_add (lintegral_eulEps_le hB c (m + 1) hAP hr.1.le)
      (lintegral_eulEps_le hB c m hAP hr.1.le)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : (0 : ℝ) ≤ 2 * d * c.M ^ 2 * (1 + d ^ 2) := by positivity
    have hp : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)
    have hq : 2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ (m + 1) ≤ 2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ m :=
      div_le_div_of_nonneg_left h0 (by positivity) hp
    unfold eulDelta
    have e : 2 * (2 * d * c.M ^ 2 * (1 + d ^ 2)) / 2 ^ m =
        2 * (2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ m) := mul_div_assoc _ _ _
    rw [e]
    linarith
  · -- the pointwise bound
    refine Eventually.of_forall fun ω r hr => ?_
    have hr1 : r ≤ gridT (m + 1) (n * 2 ^ (m + 1)) := by rw [hn']; exact hr.2
    have hr2 : r ≤ gridT m (n * 2 ^ m) := by rw [hn]; exact hr.2
    have eb : ∀ i, β i (r, ω) = c.b (eulE c (m + 1) ξ B (gridIdx (m + 1) r.toNNReal) ω) i -
        c.b (eulE c m ξ B (gridIdx m r.toNNReal) ω) i := fun i => by
      simp only [β, eulDrift_eq c (m + 1) hr.1 hr1, eulDrift_eq c m hr.1 hr2]
    have eg : ∀ i l, eulDiff c (m + 1) ξ B (n * 2 ^ (m + 1)) i l (r, ω) -
        eulDiff c m ξ B (n * 2 ^ m) i l (r, ω) =
        c.σ (eulE c (m + 1) ξ B (gridIdx (m + 1) r.toNNReal) ω) i l -
          c.σ (eulE c m ξ B (gridIdx m r.toNNReal) ω) i l := fun i l => by
      rw [eulDiff_eq c (m + 1) hr.1 hr1, eulDiff_eq c m hr.1 hr2]
    unfold coefSq
    simp only [eb, eg]
    exact coefSq_euler_bound c _ _ (eulXv c (m + 1) ξ B A (r, ω)) (eulXv c m ξ B A (r, ω))

end BlockBand.SourceProcess.Stochastic.Uniqueness
