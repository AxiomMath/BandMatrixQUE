module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Analysis.Complex.Basic

/-!
# Prokhorov for countably many complex processes on a dense time set

Setting: probability spaces `(Ωs n, Ps n)` carrying a.e.-measurable complex processes
`X n a t` (`a : ℕ` indexes the words, `t ≥ t₀`). The dense times `dT t₀ j = t₀ + p/(c+1)`,
`(p, c) = unpair j`, include `t₀`; the path `pathY n ω (pair a j) = X n a (dT t₀ j) ω` lives in
`ℕ → ℂ`.

* `exists_dT_near`, `exists_seq_dT`: density in `[t₀, ∞)`.
* `OneTimeTight`: one-time tightness for `n` large; `exists_bound`: one bound for all `n`.
* `isTight_lawY` (products of closed balls) and **`exists_tendsto_lawY`** (Prokhorov).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.WordLim

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable (t₀ : ℝ)

/-- The dense times `t₀ + p/(c+1)`. -/
def dT (j : ℕ) : ℝ := t₀ + ((Nat.unpair j).1 : ℝ) / ((Nat.unpair j).2 + 1)

theorem le_dT (j : ℕ) : t₀ ≤ dT t₀ j := by
  unfold dT
  have : (0 : ℝ) ≤ ((Nat.unpair j).1 : ℝ) / ((Nat.unpair j).2 + 1) := by positivity
  linarith

theorem exists_dT_near {t : ℝ} (ht : t₀ ≤ t) {δ : ℝ} (hδ : 0 < δ) : ∃ j, |dT t₀ j - t| ≤ δ := by
  set c : ℕ := ⌈1 / δ⌉₊
  set a : ℕ := ⌊(t - t₀) * (c + 1)⌋₊
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  refine ⟨Nat.pair a c, ?_⟩
  simp only [dT, Nat.unpair_pair]
  have h1 : (a : ℝ) ≤ (t - t₀) * (c + 1) := Nat.floor_le (by nlinarith)
  have h2 : (t - t₀) * (c + 1) < a + 1 := Nat.lt_floor_add_one _
  have h3 : 1 / δ ≤ c := Nat.le_ceil _
  have h4 : 1 ≤ δ * (c + 1) := by rw [div_le_iff₀ hδ] at h3; nlinarith
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le]
    have : t - t₀ - δ ≤ a / (c + 1) := by
      rw [le_div_iff₀ hc1]; nlinarith
    linarith
  · rw [sub_le_iff_le_add]
    have : (a : ℝ) / (c + 1) ≤ t - t₀ := by rw [div_le_iff₀ hc1]; linarith
    linarith

theorem exists_seq_dT {t : ℝ} (ht : t₀ ≤ t) :
    ∃ js : ℕ → ℕ, Tendsto (fun k => dT t₀ (js k)) atTop (𝓝 t) := by
  choose js hjs using fun k : ℕ => exists_dT_near t₀ ht (Nat.one_div_pos_of_nat (n := k))
  refine ⟨js, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hjs k)
    tendsto_one_div_add_atTop_nhds_zero_nat

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℕ → ℝ → Ωs n → ℂ}

/-- `ω ↦ (X n a (dT j) ω)_{pair a j}`. -/
def pathY (X : ∀ n, ℕ → ℝ → Ωs n → ℂ) (n : ℕ) (ω : Ωs n) : ℕ → ℂ :=
  fun i => X n (Nat.unpair i).1 (dT t₀ (Nat.unpair i).2) ω

/-- A.e.-measurable marginals at times `≥ t₀`. -/
def AEMeas (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℕ → ℝ → Ωs n → ℂ) : Prop :=
  ∀ n a t, t₀ ≤ t → AEMeasurable (X n a t) (Ps n)

variable {t₀}

theorem aemeasurable_pathY (hX : AEMeas t₀ Ps X) (n : ℕ) : AEMeasurable (pathY t₀ X n) (Ps n) :=
  AEMeasurable.of_eval fun _ => hX n _ _ (le_dT t₀ _)

variable (t₀) in
/-- The law of the path. -/
def lawY (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (X : ∀ n, ℕ → ℝ → Ωs n → ℂ) (n : ℕ) : ProbabilityMeasure (ℕ → ℂ) :=
  ⟨(Ps n).map (pathY t₀ X n), inferInstance⟩

variable (t₀) in
/-- **One-time tightness** (for `n` large). -/
def OneTimeTight (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℕ → ℝ → Ωs n → ℂ) : Prop :=
  ∀ a t, t₀ ≤ t → ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (N : ℕ), ∀ n, N ≤ n →
    Ps n {ω | M < ‖X n a t ω‖} ≤ ENNReal.ofReal θ

theorem exists_bound_one [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X) {a : ℕ}
    {t : ℝ} (ht : t₀ ≤ t) (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ m : ℕ, Ps n {ω | (m : ℝ) < ‖X n a t ω‖} ≤ ENNReal.ofReal θ := by
  have hf : AEMeasurable (fun ω => ‖X n a t ω‖) (Ps n) := (hX n a t ht).norm
  have hT := tendsto_measure_iInter_atTop (μ := Ps n)
    (s := fun m : ℕ => {ω | (m : ℝ) < ‖X n a t ω‖})
    (fun m => nullMeasurableSet_lt aemeasurable_const hf)
    (fun m m' hmm' ω (hω : (m' : ℝ) < _) =>
      show (m : ℝ) < _ from lt_of_le_of_lt (Nat.cast_le.2 hmm') hω) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ m : ℕ, {ω | (m : ℝ) < ‖X n a t ω‖}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨⌈‖X n a t ω‖⌉₊, Nat.le_ceil _⟩
  rw [he, measure_empty] at hT
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  exact ⟨m, hm.le⟩

/-- **One bound for all `n`.** -/
theorem exists_bound [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hT : OneTimeTight t₀ Ps X) {a : ℕ} {t : ℝ} (ht : t₀ ≤ t) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ n, Ps n {ω | M < ‖X n a t ω‖} ≤ ENNReal.ofReal θ := by
  obtain ⟨M₀, N, hN⟩ := hT a t ht θ hθ
  choose ms hms using fun n => exists_bound_one hX (a := a) ht n hθ
  refine ⟨max M₀ (((Finset.range N).sup ms : ℕ) : ℝ), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · refine le_trans (measure_mono fun ω hω => ?_) (hms n)
    have : (ms n : ℝ) ≤ (((Finset.range N).sup ms : ℕ) : ℝ) := by
      exact_mod_cast Finset.le_sup (f := ms) (Finset.mem_range.2 hn)
    exact show (ms n : ℝ) < _ from lt_of_le_of_lt (this.trans (le_max_right _ _)) hω
  · refine le_trans (measure_mono fun ω (hω : max M₀ _ < ‖X n a t ω‖) => ?_) (hN n hn)
    exact show M₀ < _ from lt_of_le_of_lt (le_max_left _ _) hω

/-- **The path laws are tight.** -/
theorem isTight_lawY [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hT : OneTimeTight t₀ Ps X) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (ℕ → ℂ)) : Measure (ℕ → ℂ)) |
      μ ∈ range (lawY t₀ Ps X)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨θ, hθ, hθε⟩ : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, by rw [ENNReal.ofReal_toReal hne]⟩
  choose M hM using fun i : ℕ => exists_bound hX hT (a := (Nat.unpair i).1)
    (le_dT t₀ (Nat.unpair i).2) (θ := θ / 2 / 2 ^ i) (by positivity)
  let K : Set (ℕ → ℂ) := Set.univ.pi fun i => Metric.closedBall 0 (M i)
  refine ⟨K, isCompact_univ_pi fun i => isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨μ, ⟨n, rfl⟩, rfl⟩
  have hsub : Kᶜ ⊆ ⋃ i, {ω : ℕ → ℂ | M i < ‖ω i‖} := by
    intro ω hω
    simp only [K, mem_compl_iff, mem_univ_pi, Metric.mem_closedBall, dist_zero_right,
      not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact mem_iUnion.2 ⟨i, hi⟩
  have hmeas : ∀ i, MeasurableSet {ω : ℕ → ℂ | M i < ‖ω i‖} := fun i =>
    measurableSet_lt measurable_const ((measurable_pi_apply i).norm)
  calc ((lawY t₀ Ps X n : ProbabilityMeasure (ℕ → ℂ)) : Measure (ℕ → ℂ)) Kᶜ
      ≤ ∑' i, ((Ps n).map (pathY t₀ X n)) {ω : ℕ → ℂ | M i < ‖ω i‖} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ = ∑' i, Ps n {ω | M i < ‖X n (Nat.unpair i).1 (dT t₀ (Nat.unpair i).2) ω‖} := by
        congr 1; funext i
        rw [Measure.map_apply_of_aemeasurable (aemeasurable_pathY hX n) (hmeas i)]
        rfl
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (θ / 2 / 2 ^ i) := ENNReal.tsum_le_tsum fun i => hM i n
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_two' θ)), tsum_geometric_two']
    _ ≤ ε := hθε

/-- **Prokhorov extraction.** -/
theorem exists_tendsto_lawY [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hT : OneTimeTight t₀ Ps X) :
    ∃ (Q : ProbabilityMeasure (ℕ → ℂ)) (ms : ℕ → ℕ), StrictMono ms ∧
      Tendsto (fun n => lawY t₀ Ps X (ms n)) atTop (𝓝 Q) := by
  have hc := isCompact_closure_of_isTightMeasureSet (isTight_lawY hX hT)
  obtain ⟨Q, -, ms, hms, hlim⟩ := hc.tendsto_subseq (x := lawY t₀ Ps X)
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨Q, ms, hms, hlim⟩

end BlockBand.SourceProcess.FullSourceGenerator.WordLim
