module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.PredInd
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableSampling
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Left-endpoint sampling and predictability on arbitrary filtered spaces

Setting: an arbitrary measurable space `(Ω, m₀)`, a raw filtration `𝓖` (no completion), the
raw predictable σ-algebra `predictableSpace (toCF 𝓖)` on `ℝ × Ω`; time is read as
`s.toNNReal`. This extends the left-endpoint sampling and continuity results of
`Integral` (which are specific to `DriverSample`, `dt ⊗ P` and the augmented filtration) to
arbitrary `Ω`, `𝓖` and measures.

* `leftSample n V (s, ω) = V_{k 2⁻ⁿ}(ω)` for `s ∈ (k 2⁻ⁿ, (k+1) 2⁻ⁿ]`, `0` for `s ≤ 0`;
  `stronglyMeasurable_leftSample`: raw predictable (everywhere, no null sets) whenever
  `V_t` is `𝓖_t`-strongly measurable for every `t`.
* `aestronglyMeasurable_of_leftLimit`: for any measure `μ` on `ℝ × Ω` with `s > 0` a.e., if
  `V_{u_n}(ω) → G(s, ω)` along every `u_n < s`, `u_n → s` (for `μ`-a.e. `(s, ω)`), then `G`
  is `μ`-a.e. raw predictable.
* `stoppedComposite τ φ Y (s, ω) = φ(Y_s ω) 1{s ≤ τ ω}`;
  `tendsto_leftSample_stoppedComposite`: on every continuous path, for every `s > 0`, the left
  samples of `V_t = φ(Y_t) 1{t < τ}` converge to it (pathwise, no measure).
* **`aestronglyMeasurable_stoppedComposite`**: `Y` `𝓖`-adapted with a.s. continuous
  paths, `φ` continuous, `τ` a raw `𝓖`-stopping time, `μ ≪ dt ⊗ Q` on `(0,T] × Ω`
  (`timeProbMeasure T Q`; e.g. the bracket measure `ν_T`): the stopped composite is `μ`-a.e.
  raw predictable. `stoppedCompositeL2`: its class in `PredL2 𝓖 μ` when bounded, `μ` finite.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion.PredictableRectangle
open BlockBand.SourceProcess.Stochastic.Integral (dyadicStep leftPoint mem_Ioc_iff_eq_ceil
  leftPoint_lt tendsto_leftPoint)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓖 : Filtration ℝ≥0 mΩ)

/-- Left-endpoint dyadic sampling of `V` at mesh `2⁻ⁿ`. -/
def leftSample (n : ℕ) (V : ℝ≥0 → Ω → ℝ) (p : ℝ × Ω) : ℝ :=
  if 0 < p.1 then V (leftPoint n p.1) p.2 else 0

omit mΩ in
theorem coefficientRectangle_dyadic' (n k : ℕ) (V : ℝ≥0 → Ω → ℝ) (p : ℝ × Ω) :
    coefficientRectangle ((k : ℝ≥0) * dyadicStep n) (((k + 1 : ℕ) : ℝ≥0) * dyadicStep n)
      (V ((k : ℝ≥0) * dyadicStep n)) p =
      if 0 < p.1 then (if k = ⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1 then
        V (leftPoint n p.1) p.2 else 0) else 0 := by
  classical
  unfold coefficientRectangle
  by_cases hp : 0 < p.1
  · rw [ite_eq_left hp]
    by_cases hk : k = ⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1
    · have hmem := (mem_Ioc_iff_eq_ceil n k hp).2 hk
      rw [Set.indicator_of_mem (Set.mk_mem_prod hmem (Set.mem_univ p.2)), ite_eq_left hk,
        leftPoint, ← hk]
    · rw [ite_eq_right hk, Set.indicator_of_notMem]
      exact fun h => hk ((mem_Ioc_iff_eq_ceil n k hp).1 (Set.mem_prod.1 h).1)
  · rw [ite_eq_right hp, Set.indicator_of_notMem]
    intro h
    have h1 := (Set.mem_prod.1 h).1.1
    have h2 : (0 : ℝ) ≤ (((k : ℝ≥0) * dyadicStep n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    exact hp (h2.trans_lt h1)

/-- The left-endpoint sampling of a `𝓖`-adapted family is raw predictable. -/
theorem stronglyMeasurable_leftSample (n : ℕ) {V : ℝ≥0 → Ω → ℝ}
    (hV : ∀ t, StronglyMeasurable[𝓖 t] (V t)) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)] (leftSample n V) := by
  classical
  let R : ℕ → ℝ × Ω → ℝ := fun k =>
    coefficientRectangle ((k : ℝ≥0) * dyadicStep n) (((k + 1 : ℕ) : ℝ≥0) * dyadicStep n)
      (V ((k : ℝ≥0) * dyadicStep n))
  have hR (k : ℕ) : StronglyMeasurable[predictableSpace (toCF 𝓖)] (R k) :=
    stronglyMeasurable_coefficientRectangle (toCF 𝓖) (hV _).measurable
  have hS (m : ℕ) : StronglyMeasurable[predictableSpace (toCF 𝓖)]
      (∑ k ∈ Finset.range m, R k) :=
    Finset.sum_induction _ (fun f => StronglyMeasurable[predictableSpace (toCF 𝓖)] f)
      (fun _ _ ha hb => ha.add hb) stronglyMeasurable_const (fun k _ => hR k)
  refine @stronglyMeasurable_of_tendsto _ _ _ (predictableSpace (toCF 𝓖)) _ _ atTop _ _ _ _ hS ?_
  rw [tendsto_pi_nhds]
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1)] with m hm
  rw [Finset.sum_apply]
  simp only [R, coefficientRectangle_dyadic', leftSample]
  by_cases hp : 0 < p.1
  · simp only [ite_eq_left hp]
    rw [Finset.sum_ite_eq' (Finset.range m), ite_eq_left (Finset.mem_range.2 hm)]
  · simp only [ite_eq_right hp, Finset.sum_const_zero]

/-- **Left-limit criterion for raw predictability**, for an arbitrary measure `μ`. -/
theorem aestronglyMeasurable_of_leftLimit {μ : Measure (ℝ × Ω)} {V : ℝ≥0 → Ω → ℝ}
    (hV : ∀ t, StronglyMeasurable[𝓖 t] (V t)) {G : ℝ × Ω → ℝ}
    (hpos : ∀ᵐ p ∂μ, 0 < p.1)
    (hG : ∀ᵐ p ∂μ, ∀ u : ℕ → ℝ≥0, (∀ n, (u n : ℝ) < p.1) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 p.1) → Tendsto (fun n => V (u n) p.2) atTop (𝓝 (G p))) :
    AEStronglyMeasurable[predictableSpace (toCF 𝓖)] G μ := by
  refine Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub (f := fun n => leftSample n V)
    (fun n => (stronglyMeasurable_leftSample 𝓖 n hV).aestronglyMeasurable) ?_
  filter_upwards [hG, hpos] with p hp hs
  have h := hp (fun n => leftPoint n p.1) (fun n => leftPoint_lt n hs) (tendsto_leftPoint hs)
  simpa only [leftSample, ite_eq_left hs] using h

variable {E : Type*} [TopologicalSpace E]

omit mΩ in
/-- The stopped composite `(s, ω) ↦ φ(Y_s ω) 1{s ≤ τ ω}`. -/
def stoppedComposite (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) (p : ℝ × Ω) : ℝ :=
  if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 then φ (Y p.1.toNNReal p.2) else 0

omit mΩ [TopologicalSpace E] in
theorem stoppedComposite_eq_indicator (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) :
    stoppedComposite τ φ Y = (stopSet τ).indicator fun p => φ (Y p.1.toNNReal p.2) := by
  funext p
  by_cases hp : p ∈ stopSet τ
  · rw [indicator_of_mem hp]; exact ite_eq_left hp
  · rw [indicator_of_notMem hp]; exact ite_eq_right hp

omit mΩ in
/-- The adapted family `V_t = φ(Y_t) 1{t < τ}` whose left limits give the stopped composite. -/
def preComposite (τ : Ω → WithTop ℝ≥0) (φ : E → ℝ) (Y : ℝ≥0 → Ω → E) (t : ℝ≥0) : Ω → ℝ :=
  {ω | (t : WithTop ℝ≥0) < τ ω}.indicator fun ω => φ (Y t ω)

theorem stronglyMeasurable_preComposite {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    {φ : E → ℝ} (hφ : Continuous φ) {Y : ℝ≥0 → Ω → E} (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t))
    (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (preComposite τ φ Y t) := by
  have hset : {ω | (t : WithTop ℝ≥0) < τ ω} = {ω | τ ω ≤ t}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  refine (hφ.comp_stronglyMeasurable (hY t)).indicator ?_
  rw [hset]
  exact (hτ t).compl

omit mΩ in
/-- **Pathwise left limits**: on a continuous path, for `s > 0`, `V_{u_n} → φ(Y_s) 1{s ≤ τ}`
along every `u_n < s`, `u_n → s`. -/
theorem tendsto_preComposite (τ : Ω → WithTop ℝ≥0) {φ : E → ℝ} (hφ : Continuous φ)
    {Y : ℝ≥0 → Ω → E} {p : ℝ × Ω} (hp : Continuous fun t => Y t p.2) (u : ℕ → ℝ≥0)
    (hu : ∀ n, (u n : ℝ) < p.1) (hlim : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 p.1)) :
    Tendsto (fun n => preComposite τ φ Y (u n) p.2) atTop (𝓝 (stoppedComposite τ φ Y p)) := by
  have hpos : 0 < p.1 := (NNReal.coe_nonneg _).trans_lt (hu 0)
  set s : ℝ≥0 := p.1.toNNReal with hsdef
  have hs : (s : ℝ) = p.1 := Real.coe_toNNReal _ hpos.le
  have hlim' : Tendsto u atTop (𝓝 s) := by
    rw [← NNReal.tendsto_coe, hs]
    exact hlim
  have hus (n : ℕ) : u n < s := by
    have h := hu n
    rw [← hs] at h
    exact_mod_cast h
  by_cases hsτ : (s : WithTop ℝ≥0) ≤ τ p.2
  · have hG : stoppedComposite τ φ Y p = φ (Y s p.2) := by
      simp only [stoppedComposite, ← hsdef, hsτ, ite_true]
    rw [hG]
    have hV' (n : ℕ) : preComposite τ φ Y (u n) p.2 = φ (Y (u n) p.2) := by
      have hlt : ((u n : ℝ≥0) : WithTop ℝ≥0) < τ p.2 :=
        lt_of_lt_of_le (WithTop.coe_lt_coe.2 (hus n)) hsτ
      exact Set.indicator_of_mem (show p.2 ∈ {ω | ((u n : ℝ≥0) : WithTop ℝ≥0) < τ ω} from hlt) _
    simp only [hV']
    exact (hφ.tendsto _).comp ((hp.tendsto s).comp hlim')
  · have hG : stoppedComposite τ φ Y p = 0 := by
      simp only [stoppedComposite, ← hsdef, hsτ, ite_false]
    rw [hG]
    have hlt : τ p.2 < (s : WithTop ℝ≥0) := lt_of_not_ge hsτ
    obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← hσ, WithTop.coe_lt_coe] at hlt
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim'.eventually (lt_mem_nhds hlt)] with n hn
    have hnot : p.2 ∉ {ω | ((u n : ℝ≥0) : WithTop ℝ≥0) < τ ω} := by
      simp only [mem_ofPred_eq, ← hσ, WithTop.coe_lt_coe, not_lt]
      exact hn.le
    exact (Set.indicator_of_notMem hnot _).symm

omit mΩ in
/-- On a continuous path, the left samples converge to the stopped composite at every `s > 0`. -/
theorem tendsto_leftSample_stoppedComposite (τ : Ω → WithTop ℝ≥0) {φ : E → ℝ}
    (hφ : Continuous φ) {Y : ℝ≥0 → Ω → E} {p : ℝ × Ω} (hp : Continuous fun t => Y t p.2)
    (hs : 0 < p.1) :
    Tendsto (fun n => leftSample n (preComposite τ φ Y) p) atTop
      (𝓝 (stoppedComposite τ φ Y p)) := by
  simpa only [leftSample, ite_eq_left hs] using tendsto_preComposite τ hφ hp
    (fun n => leftPoint n p.1) (fun n => leftPoint_lt n hs) (tendsto_leftPoint hs)

theorem ae_timeProb_snd {Q : Measure Ω} [SFinite Q] {T : ℝ≥0} {q : Ω → Prop}
    (hq : ∀ᵐ ω ∂Q, q ω) : ∀ᵐ p ∂timeProbMeasure T Q, q p.2 :=
  (Measure.quasiMeasurePreserving_snd).ae hq

theorem ae_timeProb_mem (Q : Measure Ω) [SFinite Q] (T : ℝ≥0) :
    ∀ᵐ p ∂timeProbMeasure T Q, p.1 ∈ Ioc (0 : ℝ) T :=
  (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioc)

/-- **Predictability of stopped continuous composites on arbitrary `Ω`.** -/
theorem aestronglyMeasurable_stoppedComposite {Q : Measure Ω} [SFinite Q] {T : ℝ≥0}
    {μ : Measure (ℝ × Ω)} (hμ : μ ≪ timeProbMeasure T Q) {Y : ℝ≥0 → Ω → E}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {φ : E → ℝ} (hφ : Continuous φ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    AEStronglyMeasurable[predictableSpace (toCF 𝓖)] (stoppedComposite τ φ Y) μ := by
  refine Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub
    (f := fun n => leftSample n (preComposite τ φ Y))
    (fun n => (stronglyMeasurable_leftSample 𝓖 n
      (stronglyMeasurable_preComposite 𝓖 hτ hφ hY)).aestronglyMeasurable) ?_
  filter_upwards [hμ.ae_le (ae_timeProb_snd (T := T) hYc), hμ.ae_le (ae_timeProb_mem Q T)]
    with p hp hpos
  exact tendsto_leftSample_stoppedComposite τ hφ hp hpos.1

theorem memLp_stoppedComposite {Q : Measure Ω} [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    [IsFiniteMeasure μ] (hμ : μ ≪ timeProbMeasure T Q) {Y : ℝ≥0 → Ω → E}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {φ : E → ℝ} (hφ : Continuous φ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {C : ℝ}
    (hC : ∀ p, |stoppedComposite τ φ Y p| ≤ C) : MemLp (stoppedComposite τ φ Y) 2 μ :=
  MemLp.of_bound ((aestronglyMeasurable_stoppedComposite 𝓖 hμ hY hYc hφ hτ).mono
    (predictableSpace_le _)) C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC p)

/-- The class of a bounded stopped composite in `PredL2 𝓖 μ` (`μ` finite, `μ ≪ dt ⊗ Q`). -/
def stoppedCompositeL2 {Q : Measure Ω} [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    [IsFiniteMeasure μ] (hμ : μ ≪ timeProbMeasure T Q) {Y : ℝ≥0 → Ω → E}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {φ : E → ℝ} (hφ : Continuous φ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {C : ℝ}
    (hC : ∀ p, |stoppedComposite τ φ Y p| ≤ C) : PredL2 𝓖 μ :=
  ⟨(memLp_stoppedComposite 𝓖 hμ hY hYc hφ hτ hC).toLp _,
    mem_lpMeas_iff_aestronglyMeasurable.2
      ((aestronglyMeasurable_stoppedComposite 𝓖 hμ hY hYc hφ hτ).congr
        (MemLp.coeFn_toLp _).symm)⟩

theorem stoppedCompositeL2_coeFn {Q : Measure Ω} [SFinite Q] {T : ℝ≥0} {μ : Measure (ℝ × Ω)}
    [IsFiniteMeasure μ] (hμ : μ ≪ timeProbMeasure T Q) {Y : ℝ≥0 → Ω → E}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {φ : E → ℝ} (hφ : Continuous φ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {C : ℝ}
    (hC : ∀ p, |stoppedComposite τ φ Y p| ≤ C) :
    (((stoppedCompositeL2 𝓖 hμ hY hYc hφ hτ hC : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ]
      stoppedComposite τ φ Y :=
  MemLp.coeFn_toLp (memLp_stoppedComposite 𝓖 hμ hY hYc hφ hτ hC)

/-- The bracket measure is absolutely continuous w.r.t. `dt ⊗ Q` on `(0,T]`. -/
theorem bracketMeasure_absolutelyContinuous (Q : Measure Ω) (α : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    bracketMeasure Q α T ≪ timeProbMeasure T Q :=
  withDensity_absolutelyContinuous _ _

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
