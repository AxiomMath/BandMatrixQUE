module

public import BlockBand.Endpoints.Response.NearSchattenProkhorovPath
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Prokhorov extraction for dyadic grid laws, and a.s. continuity of the limit grid paths

* `NspTightAt`: at each `t ≥ t₀`, the coordinates are tight, eventually in `n`;
* `NspModulus`: on each `[t₀, T]`, the sup-modulus is asymptotically small in (outer)
  probability.

Results.
* `nsp_isTight_gridLaw`: the laws `nspGridLaw n` on the Polish space `ι × ℕ × ℕ → ℂ` of the
  values at the dyadic times `nspTime t₀ k j` form a tight set (a single finite measure is tight
  at each coordinate, so finitely many early `n` are absorbed).
* `nsp_exists_tendsto_gridLaw`: Prokhorov (Mathlib, `isCompact_closure_of_isTightMeasureSet`)
  gives, along any sequence, a convergent subsequence.
* `nsp_ae_gridGood`: under a limit law every grid path is a.s. good (`NspGridGood`), by the
  portmanteau theorem on the open grid-oscillation sets and the modulus hypothesis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {ι : Type} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Tightness of the coordinates at each time `t ≥ t₀`, eventually in `n`. -/
def NspTightAt (t₀ : ℝ) (P : ∀ n, Measure (Ω n)) (X : ∀ n, ι → ℝ → Ω n → ℂ) : Prop :=
  ∀ (i : ι) (t : ℝ), t₀ ≤ t → ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (n₀ : ℕ), ∀ n, n₀ ≤ n →
    P n {ω | M < ‖X n i t ω‖} ≤ ENNReal.ofReal θ

/-- Asymptotically small sup-modulus on each `[t₀, T]`, in outer probability. -/
def NspModulus (t₀ : ℝ) (P : ∀ n, Measure (Ω n)) (X : ∀ n, ι → ℝ → Ω n → ℂ) : Prop :=
  ∀ (i : ι) (T : ℝ), t₀ < T → ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    P n {ω | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ δ ∧ η < ‖X n i t ω - X n i t' ω‖} ≤
      ENNReal.ofReal θ

/-- The dyadic grid values of the `n`-th process. -/
def nspGrid (t₀ : ℝ) (X : ∀ n, ι → ℝ → Ω n → ℂ) (n : ℕ) (ω : Ω n) : ι × ℕ × ℕ → ℂ :=
  fun c => X n c.1 (nspTime t₀ c.2.1 c.2.2) ω

theorem nsp_measurable_grid (t₀ : ℝ) {X : ∀ n, ι → ℝ → Ω n → ℂ}
    (hX : ∀ n i t, Measurable (X n i t)) (n : ℕ) : Measurable (nspGrid t₀ X n) :=
  Measurable.of_eval fun c => hX n c.1 _

/-- The law of the dyadic grid values of the `n`-th process. -/
def nspGridLaw (t₀ : ℝ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, ι → ℝ → Ω n → ℂ) (n : ℕ) :
    ProbabilityMeasure (ι × ℕ × ℕ → ℂ) :=
  ⟨(P n).map (nspGrid t₀ X n), inferInstance⟩

theorem nsp_gridLaw_apply (t₀ : ℝ) {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t)) (n : ℕ)
    {s : Set (ι × ℕ × ℕ → ℂ)} (hs : MeasurableSet s) :
    ((nspGridLaw t₀ P X n : ProbabilityMeasure _) : Measure _) s = P n (nspGrid t₀ X n ⁻¹' s) :=
  Measure.map_apply (nsp_measurable_grid t₀ hX n) hs

/-- A single finite measure has small tails. -/
theorem nsp_tail_small {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℂ} (hf : Measurable f) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, μ {ω | M < ‖f ω‖} ≤ ENNReal.ofReal θ := by
  let s : ℕ → Set α := fun k => {ω | (k : ℝ) < ‖f ω‖}
  have hs : ∀ k, NullMeasurableSet (s k) μ := fun k =>
    (measurableSet_lt measurable_const hf.norm).nullMeasurableSet
  have hm : Antitone s := fun a b hab ω (hω : (b : ℝ) < ‖f ω‖) =>
    show (a : ℝ) < ‖f ω‖ from lt_of_le_of_lt (by exact_mod_cast hab) hω
  have h0 : (⋂ k, s k) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt ‖f ω‖
    exact ⟨k, fun h : (k : ℝ) < ‖f ω‖ => absurd h (not_lt.2 hk.le)⟩
  have ht := tendsto_measure_iInter_atTop hs hm ⟨0, measure_ne_top _ _⟩
  rw [h0, measure_empty] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  exact ⟨k, hk.le⟩

/-- Uniform tail bound for all `n` at one coordinate. -/
theorem nsp_tail_uniform {t₀ : ℝ} {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t))
    (hT : NspTightAt t₀ P X) (i : ι) {t : ℝ} (ht : t₀ ≤ t) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ n, P n {ω | M < ‖X n i t ω‖} ≤ ENNReal.ofReal θ := by
  obtain ⟨M₁, n₀, h₁⟩ := hT i t ht θ hθ
  have hfin : ∀ K : ℕ, ∃ M : ℝ, ∀ n, n < K → P n {ω | M < ‖X n i t ω‖} ≤ ENNReal.ofReal θ := by
    intro K
    induction K with
    | zero => exact ⟨0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    | succ K ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨M', hM'⟩ := nsp_tail_small (P K) (hX K i t) hθ
      refine ⟨max M M', fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · exact (measure_mono fun ω (hω : max M M' < _) => lt_of_le_of_lt (le_max_left _ _) hω).trans
          (hM n hn)
      · exact (measure_mono fun ω (hω : max M M' < _) => lt_of_le_of_lt (le_max_right _ _) hω).trans
          hM'
  obtain ⟨M₂, h₂⟩ := hfin n₀
  refine ⟨max M₁ M₂, fun n => ?_⟩
  rcases lt_or_ge n n₀ with hn | hn
  · exact (measure_mono fun ω (hω : max M₁ M₂ < _) => lt_of_le_of_lt (le_max_right _ _) hω).trans
      (h₂ n hn)
  · exact (measure_mono fun ω (hω : max M₁ M₂ < _) => lt_of_le_of_lt (le_max_left _ _) hω).trans
      (h₁ n hn)

/-- **Tightness of the grid laws** on `ι × ℕ × ℕ → ℂ`. -/
theorem nsp_isTight_gridLaw [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t))
    (hT : NspTightAt t₀ P X) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (ι × ℕ × ℕ → ℂ)) : Measure (ι × ℕ × ℕ → ℂ)) |
      μ ∈ range (nspGridLaw t₀ P X)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' (ι × ℕ × ℕ)
  have hM : ∀ c : ι × ℕ × ℕ, ∃ M : ℝ, ∀ n,
      P n {ω | M < ‖X n c.1 (nspTime t₀ c.2.1 c.2.2) ω‖} ≤ ENNReal.ofReal (ε' c) := fun c =>
    nsp_tail_uniform hX hT c.1 (nsp_le_time t₀ _ _) (NNReal.coe_pos.2 (hε'pos c))
  choose M hM using hM
  refine ⟨Set.pi univ fun c => Metric.closedBall 0 (M c),
    isCompact_univ_pi fun c => isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  have hsub : (Set.pi univ fun c => Metric.closedBall (0 : ℂ) (M c))ᶜ ⊆
      ⋃ c : ι × ℕ × ℕ, {x : ι × ℕ × ℕ → ℂ | M c < ‖x c‖} := by
    intro x hx
    simp only [mem_compl_iff, mem_univ_pi, Metric.mem_closedBall, dist_zero_right,
      not_forall, not_le] at hx
    exact mem_iUnion.2 hx
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  refine le_trans ?_ hε'sum.le
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [nsp_gridLaw_apply t₀ hX n (measurableSet_lt measurable_const (measurable_pi_apply c).norm)]
  exact (hM c n).trans (by rw [ENNReal.ofReal_coe_nnreal])

/-- **Prokhorov extraction** for the grid laws. -/
theorem nsp_exists_tendsto_gridLaw [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {X : ∀ n, ι → ℝ → Ω n → ℂ}
    (hX : ∀ n i t, Measurable (X n i t)) (hT : NspTightAt t₀ P X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ProbabilityMeasure (ι × ℕ × ℕ → ℂ),
      Tendsto (fun n => nspGridLaw t₀ P X (φ n)) atTop (𝓝 ν) := by
  have hK := isCompact_closure_of_isTightMeasureSet (nsp_isTight_gridLaw hX hT)
  obtain ⟨ν, -, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := nspGridLaw t₀ P X) fun n => subset_closure ⟨n, rfl⟩
  exact ⟨φ, hφ, ν, hlim⟩

/-- The grid-oscillation event of the coordinate `i`, as a set of grid paths. -/
def nspOscSet (t₀ : ℝ) (i : ι) (N : ℕ) (η δ : ℝ) : Set (ι × ℕ × ℕ → ℂ) :=
  {x | NspGridOsc t₀ (fun p => x (i, p)) N η δ}

theorem nsp_isOpen_oscSet (t₀ : ℝ) (i : ι) (N : ℕ) (η δ : ℝ) :
    IsOpen (nspOscSet t₀ i N η δ) := by
  simp only [nspOscSet, NspGridOsc, ofPred_exists]
  refine isOpen_iUnion fun k => isOpen_iUnion fun j => isOpen_iUnion fun k' =>
    isOpen_iUnion fun j' => ?_
  simp only [ofPred_and]
  exact isOpen_const.inter (isOpen_const.inter (isOpen_const.inter
    (isOpen_lt continuous_const (by fun_prop))))

/-- Under a limit law, the oscillation sets have small mass. -/
theorem nsp_limit_oscSet_le [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t))
    (hC : NspModulus t₀ P X) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ν : ProbabilityMeasure (ι × ℕ × ℕ → ℂ)}
    (hν : Tendsto (fun n => nspGridLaw t₀ P X (φ n)) atTop (𝓝 ν)) (i : ι) (N : ℕ)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ', δ' ≤ δ → (ν : Measure _) (nspOscSet t₀ i N η δ') ≤ ENNReal.ofReal θ := by
  obtain ⟨δ, hδ, n₀, hn₀⟩ := hC i (t₀ + N + 1) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) η θ hη hθ
  refine ⟨δ, hδ, fun δ' hδ' => ?_⟩
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν
    (nsp_isOpen_oscSet t₀ i N η δ')).trans ?_
  refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [nsp_gridLaw_apply t₀ hX _ (nsp_isOpen_oscSet t₀ i N η δ').measurableSet]
  refine (measure_mono ?_).trans (hn₀ (φ n) (hn.trans (hφ.id_le n)))
  rintro ω ⟨k, j, k', j', h₁, h₂, h₃, h₄⟩
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact ⟨_, ⟨nsp_le_time t₀ k j, by linarith⟩, _, ⟨nsp_le_time t₀ k' j', by linarith⟩,
    h₃.trans hδ', h₄⟩

/-- **A.s. good grid paths** under any limit of the grid laws. -/
theorem nsp_ae_gridGood [Countable ι] {t₀ : ℝ} {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, ι → ℝ → Ω n → ℂ} (hX : ∀ n i t, Measurable (X n i t))
    (hC : NspModulus t₀ P X) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ν : ProbabilityMeasure (ι × ℕ × ℕ → ℂ)}
    (hν : Tendsto (fun n => nspGridLaw t₀ P X (φ n)) atTop (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure (ι × ℕ × ℕ → ℂ)), ∀ i, NspGridGood t₀ fun p => x (i, p) := by
  have h0 : ∀ (i : ι) (N k : ℕ), (ν : Measure _)
      (⋂ j : ℕ, nspOscSet t₀ i N (1 / ((k : ℝ) + 1)) (1 / ((j : ℝ) + 1))) = 0 := by
    intro i N k
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun θ hθ _ => ?_) zero_le
    obtain ⟨δ, hδ, hle⟩ := nsp_limit_oscSet_le hX hC hφ hν i N (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
      (NNReal.coe_pos.2 hθ)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
    exact (measure_mono (iInter_subset _ j)).trans (hle _ hj.le)
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun N =>
    measure_iUnion_null fun k => h0 i N k)
  intro x hx
  simp only [NspGridGood, mem_ofPred_eq, not_forall, not_exists, not_not] at hx
  obtain ⟨i, N, k, hk⟩ := hx
  exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨N, mem_iUnion.2 ⟨k, mem_iInter.2 fun j => hk j⟩⟩⟩

end BlockBand.Endpoints
