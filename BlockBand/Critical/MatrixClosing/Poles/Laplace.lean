module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Multivariate Laplace continuity theorem for nonnegative random vectors

* `tendstoInDistribution_of_laplace`: let `Z_N`, `Z` be random vectors in `ι → ℝ` (`ι` finite)
  with nonnegative coordinates on probability spaces `(Ω N, P N)`, `(Ω', P')`. If
  `E exp(-Σ_k t_k Z_{N,k}) → E exp(-Σ_k t_k Z_k)` for every `t ∈ [0,∞)^ι`, then `Z_N ⇒ Z` in law.

Proof: tightness from the Laplace transform of `Σ_k Z_{N,k}` near `t = 0` (Markov bound
`P(T > r)(1 - e^{-sr}) ≤ 1 - E e^{-sT}`, Mathlib
`isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt`), then Mathlib
`ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` with the algebra spanned by
`y ↦ exp(-Σ_k t_k ψ(y_k))`, `ψ(y) = max(y, arctan y)` (the identity on `[0,∞)`, strictly increasing
and bounded below, so these tests are bounded and separate the points of `ℝ^ι`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

/-!
## The shift `ψ(y) = max(y, arctan y)`
-/

/-- `ψ(y) = max(y, arctan y)`: the identity on `[0, ∞)`, strictly increasing, `> -π/2`. -/
def lapShift (y : ℝ) : ℝ := max y (Real.arctan y)

theorem continuous_lapShift : Continuous lapShift :=
  continuous_id.max Real.continuous_arctan

theorem lapShift_of_nonneg {y : ℝ} (hy : 0 ≤ y) : lapShift y = y :=
  max_eq_left (Real.arctan_le_self hy)

theorem lapShift_strictMono : StrictMono lapShift := fun _ _ h =>
  max_lt (lt_of_lt_of_le h (le_max_left _ _))
    (lt_of_lt_of_le (Real.arctan_strictMono h) (le_max_right _ _))

theorem neg_pi_div_two_lt_lapShift (y : ℝ) : -(Real.pi / 2) < lapShift y :=
  lt_of_lt_of_le (Real.neg_pi_div_two_lt_arctan y) (le_max_right _ _)

/-!
## Laplace tests
-/

variable {ι : Type*} [Fintype ι]

/-- `y ↦ exp(-Σ_k t_k ψ(y_k))`. -/
def lapFun (t : ι → ℝ≥0) (y : ι → ℝ) : ℝ := Real.exp (-∑ k, (t k : ℝ) * lapShift (y k))

theorem continuous_lapFun (t : ι → ℝ≥0) : Continuous (lapFun t) :=
  Real.continuous_exp.comp (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_lapShift.comp (continuous_apply k))).neg

theorem lapFun_le (t : ι → ℝ≥0) (y : ι → ℝ) :
    lapFun t y ≤ Real.exp (∑ k, (t k : ℝ) * (Real.pi / 2)) := by
  unfold lapFun
  refine Real.exp_le_exp.2 ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := neg_pi_div_two_lt_lapShift (y k)
  have h2 : (0 : ℝ) ≤ t k := (t k).2
  nlinarith

/-- The Laplace test as a bounded continuous function. -/
def lapTest (t : ι → ℝ≥0) : (ι → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨lapFun t, continuous_lapFun t⟩
    (Real.exp (∑ k, (t k : ℝ) * (Real.pi / 2))) fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := lapFun_le t x
      have h2 := lapFun_le t y
      have h3 : 0 < lapFun t x := Real.exp_pos _
      have h4 : 0 < lapFun t y := Real.exp_pos _
      rw [abs_le]; constructor <;> linarith

theorem lapTest_apply (t : ι → ℝ≥0) (y : ι → ℝ) : lapTest t y = lapFun t y := rfl

theorem lapTest_apply_of_nonneg (t : ι → ℝ≥0) {y : ι → ℝ} (hy : ∀ k, 0 ≤ y k) :
    lapTest t y = Real.exp (-∑ k, (t k : ℝ) * y k) := by
  rw [lapTest_apply, lapFun]
  simp only [lapShift_of_nonneg (hy _)]

theorem lapTest_mul (s t : ι → ℝ≥0) : lapTest s * lapTest t = lapTest (s + t) := by
  ext y
  simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, lapTest_apply, lapFun,
    ← Real.exp_add]
  congr 1
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, NNReal.coe_add]
  ring

theorem lapTest_zero : lapTest (0 : ι → ℝ≥0) = 1 := by
  ext y
  simp [lapTest_apply, lapFun]

/-- The span of Laplace tests. -/
abbrev lapSpan (ι : Type*) [Fintype ι] : Submodule ℝ ((ι → ℝ) →ᵇ ℝ) :=
  Submodule.span ℝ (Set.range fun t : ι → ℝ≥0 => lapTest t)

theorem lapTest_mem (t : ι → ℝ≥0) : lapTest t ∈ lapSpan ι := Submodule.subset_span ⟨t, rfl⟩

theorem lapSpan_mul_mem {f f' : (ι → ℝ) →ᵇ ℝ} (hf : f ∈ lapSpan ι) (hf' : f' ∈ lapSpan ι) :
    f * f' ∈ lapSpan ι := by
  induction hf using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, rfl⟩ := ha
    induction hf' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨t, rfl⟩ := hb
      rw [lapTest_mul]; exact lapTest_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

/-- The star algebra spanned by Laplace tests. -/
def lapAlg (ι : Type*) [Fintype ι] : StarSubalgebra ℝ ((ι → ℝ) →ᵇ ℝ) :=
  { (lapSpan ι).toSubalgebra (by rw [← lapTest_zero]; exact lapTest_mem 0)
      (fun _ _ hx hy => lapSpan_mul_mem hx hy) with
    star_mem' := fun {a} ha => by
      have : star a = a := by ext p; simp
      rw [this]; exact ha }

theorem mem_lapAlg {f : (ι → ℝ) →ᵇ ℝ} : f ∈ lapAlg ι ↔ f ∈ lapSpan ι := Iff.rfl

theorem lapFun_single [DecidableEq ι] (k : ι) (y : ι → ℝ) :
    lapFun (Pi.single k 1) y = Real.exp (-lapShift (y k)) := by
  rw [lapFun]
  congr 2
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem lapAlg_separatesPoints :
    ((lapAlg ι).map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  classical
  intro y y' hne
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  refine ⟨_, ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) (lapTest (Pi.single k 1)),
    ⟨lapTest (Pi.single k 1), lapTest_mem _, rfl⟩, rfl⟩, ?_⟩
  simp only [BoundedContinuousFunction.toContinuousMapStarₐ_apply_apply]
  rw [lapTest_apply, lapTest_apply, lapFun_single, lapFun_single]
  intro h
  exact hk (lapShift_strictMono.injective (neg_injective (Real.exp_injective h)))

/-!
## Tightness from the Laplace transform near zero
-/

/-- **Markov bound for the Laplace transform**: for `T ≥ 0`, `s > 0`, `r` with `e^{-sr} ≤ 1/2`,
`P(T > r) ≤ 2(1 - E e^{-sT})`. -/
theorem measureReal_gt_le_laplace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} (hT : AEMeasurable T P) (hT0 : ∀ ω, 0 ≤ T ω)
    {s r : ℝ} (hs : 0 < s) (hsr : Real.exp (-(s * r)) ≤ 1 / 2) :
    P.real {ω | r < T ω} ≤ 2 * (1 - ∫ ω, Real.exp (-(s * T ω)) ∂P) := by
  have hm : AEMeasurable (fun ω => 1 - Real.exp (-(s * T ω))) P :=
    aemeasurable_const.sub ((hT.const_mul s).neg.exp)
  have hb : ∀ ω, 0 ≤ 1 - Real.exp (-(s * T ω)) ∧ 1 - Real.exp (-(s * T ω)) ≤ 1 := by
    intro ω
    have h1 : Real.exp (-(s * T ω)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hs.le (hT0 ω)))
    have h2 := Real.exp_pos (-(s * T ω))
    constructor <;> linarith
  have hint : Integrable (fun ω => 1 - Real.exp (-(s * T ω))) P :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]; exact (hb ω).2)
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => (hb ω).1) hint
    (1 - Real.exp (-(s * r)))
  have hsub : {ω | r < T ω} ⊆ {ω | 1 - Real.exp (-(s * r)) ≤ 1 - Real.exp (-(s * T ω))} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : Real.exp (-(s * T ω)) ≤ Real.exp (-(s * r)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hω.le hs.le))
    linarith
  have hmono : P.real {ω | r < T ω} ≤
      P.real {ω | 1 - Real.exp (-(s * r)) ≤ 1 - Real.exp (-(s * T ω))} :=
    measureReal_mono hsub
  have hexp : ∫ ω, (1 - Real.exp (-(s * T ω))) ∂P = 1 - ∫ ω, Real.exp (-(s * T ω)) ∂P := by
    have hei : Integrable (fun ω => Real.exp (-(s * T ω))) P :=
      Integrable.of_bound ((hT.const_mul s).neg.exp).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hs.le (hT0 ω))))
    rw [integral_sub (integrable_const 1) hei]
    simp
  have hP0 : 0 ≤ P.real {ω | r < T ω} := measureReal_nonneg
  rw [hexp] at hmk
  nlinarith

theorem exp_neg_two_le_half : Real.exp (-2) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp 2
  rw [Real.exp_neg]
  have hpos := Real.exp_pos 2
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-!
## The continuity theorem
-/

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

/-- **Multivariate Laplace continuity theorem.** Random vectors with nonnegative coordinates whose
Laplace transforms converge on `[0, ∞)^ι` converge in law. -/
theorem tendstoInDistribution_of_laplace {Z : ∀ N, Ω N → ι → ℝ} {Z' : Ω' → ι → ℝ}
    (hZm : ∀ N, AEMeasurable (Z N) (P N)) (hZ'm : AEMeasurable Z' P')
    (hZ : ∀ N ω k, 0 ≤ Z N ω k) (hZ' : ∀ ω k, 0 ≤ Z' ω k)
    (hL : ∀ t : ι → ℝ≥0, Tendsto (fun N => ∫ ω, Real.exp (-∑ k, (t k : ℝ) * Z N ω k) ∂P N)
      atTop (𝓝 (∫ ω, Real.exp (-∑ k, (t k : ℝ) * Z' ω k) ∂P'))) :
    TendstoInDistribution Z atTop Z' P P' := by
  refine ⟨hZm, hZ'm, ?_⟩
  set μ : ℕ → ProbabilityMeasure (ι → ℝ) := fun N => ⟨(P N).map (Z N), inferInstance⟩
  set μ' : ProbabilityMeasure (ι → ℝ) := ⟨P'.map Z', inferInstance⟩
  have hint : ∀ N (g : (ι → ℝ) →ᵇ ℝ),
      ∫ y, g y ∂(μ N : Measure (ι → ℝ)) = ∫ ω, g (Z N ω) ∂P N := fun N g =>
    integral_map (hZm N) g.continuous.aestronglyMeasurable
  have hint' : ∀ g : (ι → ℝ) →ᵇ ℝ, ∫ y, g y ∂(μ' : Measure (ι → ℝ)) = ∫ ω, g (Z' ω) ∂P' :=
    fun g => integral_map hZ'm g.continuous.aestronglyMeasurable
  -- the sum `T = Σ_k Z_k`
  set T : ∀ N, Ω N → ℝ := fun N ω => ∑ k, Z N ω k
  set T' : Ω' → ℝ := fun ω => ∑ k, Z' ω k
  have hT0 : ∀ N ω, 0 ≤ T N ω := fun N ω => Finset.sum_nonneg fun k _ => hZ N ω k
  have hT'0 : ∀ ω, 0 ≤ T' ω := fun ω => Finset.sum_nonneg fun k _ => hZ' ω k
  have hTm : ∀ N, AEMeasurable (T N) (P N) := fun N =>
    Finset.aemeasurable_fun_sum _ fun k _ => (measurable_pi_apply k).comp_aemeasurable (hZm N)
  have hT'm : AEMeasurable T' P' :=
    Finset.aemeasurable_fun_sum _ fun k _ => (measurable_pi_apply k).comp_aemeasurable hZ'm
  have hLT : ∀ s : ℝ≥0, Tendsto (fun N => ∫ ω, Real.exp (-((s : ℝ) * T N ω)) ∂P N) atTop
      (𝓝 (∫ ω, Real.exp (-((s : ℝ) * T' ω)) ∂P')) := by
    intro s
    have h := hL (fun _ => s)
    simp only [← Finset.mul_sum] at h
    exact h
  -- continuity of the limit transform at `0`
  have hcont : Tendsto (fun s : ℝ≥0 => ∫ ω, Real.exp (-((s : ℝ) * T' ω)) ∂P') (𝓝 0) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := P') (l := 𝓝 (0 : ℝ≥0))
      (F := fun (s : ℝ≥0) ω => Real.exp (-((s : ℝ) * T' ω))) (f := fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ))
      (Eventually.of_forall fun s =>
        ((hT'm.const_mul (s : ℝ)).neg.exp).aestronglyMeasurable)
      (Eventually.of_forall fun s => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg s.2 (hT'0 ω))))
      (integrable_const 1)
      (Eventually.of_forall fun ω => by
        have : Tendsto (fun s : ℝ≥0 => Real.exp (-((s : ℝ) * T' ω))) (𝓝 0)
            (𝓝 (Real.exp (-(((0 : ℝ≥0) : ℝ) * T' ω)))) :=
          ((Real.continuous_exp.comp ((NNReal.continuous_coe.mul continuous_const).neg)).tendsto 0)
        simpa using this)
    simpa using h
  -- tightness
  have htight : IsTightMeasureSet {(μ N : Measure (ι → ℝ)) | N} := by
    have h := isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
      (μ := fun N => (μ N : Measure (ι → ℝ))) ?_
    · exact h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, -, hδpos, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hδ : 0 < δ := by simpa using hδpos
    -- choose `s > 0` with `1 - E e^{-sT'} ≤ δ/8`
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝[>] 0,
        |∫ ω, Real.exp (-((s : ℝ) * T' ω)) ∂P' - 1| < δ / 8 := by
      have := (Metric.tendsto_nhds.1 hcont) (δ / 8) (by linarith)
      simpa [Real.dist_eq] using this.filter_mono nhdsWithin_le_nhds
    obtain ⟨s, hs1, hs0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hs : (0 : ℝ) < s := hs0
    refine eventually_atTop.2 ⟨2 / s, fun r hr => ?_⟩
    have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
    have hsr : Real.exp (-((s : ℝ) * r)) ≤ 1 / 2 := by
      refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_two_le_half
      have : 2 ≤ (s : ℝ) * r := by
        have := mul_le_mul_of_nonneg_left hr hs.le
        rwa [mul_div_cancel₀ _ hs.ne'] at this
      linarith
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    have hN := (Metric.tendsto_nhds.1 (hLT s)) (δ / 8) (by linarith)
    filter_upwards [hN] with N hN
    rw [Real.dist_eq] at hN
    have hmk := measureReal_gt_le_laplace (hTm N) (hT0 N) hs hsr
    have hsub : {y : ι → ℝ | r < ‖y‖} ⊆ {y | r < ∑ k, y k} ∪ {y | ∃ k, y k < 0} := by
      intro y hy
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hy ⊢
      by_cases h0 : ∃ k, y k < 0
      · exact Or.inr h0
      · left
        push Not at h0
        refine lt_of_lt_of_le hy ?_
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun k _ => h0 k)).2 fun k => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 k)]
        exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ k)
    have hopen : MeasurableSet {y : ι → ℝ | r < ‖y‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hmap : (μ N : Measure (ι → ℝ)) {y | r < ‖y‖} = (P N) (Z N ⁻¹' {y | r < ‖y‖}) := by
      simp only [μ, ProbabilityMeasure.coe_mk]
      exact Measure.map_apply_of_aemeasurable (hZm N) hopen
    simp only [hmap]
    have hpre : Z N ⁻¹' {y | r < ‖y‖} ⊆ {ω | r < T N ω} := by
      intro ω hω
      have := hsub hω
      simp only [Set.mem_union, Set.mem_ofPred_eq] at this
      rcases this with h | ⟨k, hk⟩
      · exact h
      · exact absurd (hZ N ω k) (not_le.2 hk)
    calc (P N) (Z N ⁻¹' {y | r < ‖y‖}) ≤ (P N) {ω | r < T N ω} := measure_mono hpre
      _ = ENNReal.ofReal ((P N).real {ω | r < T N ω}) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal δ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_lt] at hs1 hN
          linarith [hs1.1, hN.1]
      _ ≤ ε := hδε.le
  refine ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℝ htight lapAlg_separatesPoints ?_
  intro g hg
  rw [mem_lapAlg] at hg
  induction hg using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨t, rfl⟩ := ha
    simp only [hint, hint']
    simp only [lapTest_apply_of_nonneg t (hZ _ _), lapTest_apply_of_nonneg t (hZ' _)]
    exact hL t
  | zero => simp
  | add a c _ _ ha hc =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    have e : ∀ ν : Measure (ι → ℝ), [IsFiniteMeasure ν] →
        ∫ y, (a y + c y) ∂ν = ∫ y, a y ∂ν + ∫ y, c y ∂ν := fun ν _ =>
      integral_add (a.integrable ν) (c.integrable ν)
    simp only [e]
    exact ha.add hc
  | smul t a _ ha =>
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, integral_const_mul]
    exact ha.const_mul t

end BlockBand.Critical.MatrixClosing.Poles
