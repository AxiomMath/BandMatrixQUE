module

public import BlockBand.Transmission.LawDuality.BorelGiry
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Prokhorov on a countable time set: subsequential laws of `(μ_n(q_j))_j`

Setting (abstract, `W`-free): a sequence of probability spaces `(Ωs n, Ps n)` carrying
a.e.-measurable random finite measures `X n t` on `[0,1]` (`t > 0`). We use the countable dense
time set `qT j = (a+1)/(c+1)`, `(a, c) = unpair j` (all positive rationals), the path map
`pathY n ω = (X n (qT j) ω)_j : ℕ → FM[0,1]` and its law `lawY n`.

* `qT_pos`, `exists_qT_near`, `exists_seq_qT`: positivity and density of the time set.
* `OneTimeTight`: one-time tightness of the masses, for `n` large.
* `exists_mass_bound`: under `OneTimeTight`, one bound `M` works for **all** `n`.
* `isTight_lawY`: the laws of the paths form a tight set on `ℕ → FM[0,1]` (product of the
  compact sets `{mass ≤ M_j}`, Mathlib `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`).
* **`exists_tendsto_lawY`**: Prokhorov (`isCompact_closure_of_isTightMeasureSet`) and the
  metrizability of `ProbabilityMeasure (ℕ → FM[0,1])` give a strictly increasing `ms` and a
  limit law `Q` with `lawY (ms n) → Q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality.SubLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

/-- The state space. -/
abbrev St := FiniteMeasure unitInterval

/-!
## The countable time set
-/

/-- `qT j = (a+1)/(c+1)` with `(a, c) = unpair j`: every positive rational. -/
def qT (j : ℕ) : ℝ := ((Nat.unpair j).1 + 1 : ℝ) / ((Nat.unpair j).2 + 1)

theorem qT_pos (j : ℕ) : 0 < qT j := by unfold qT; positivity

theorem exists_qT_near {t : ℝ} (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) : ∃ j, |qT j - t| ≤ δ := by
  set c : ℕ := ⌈1 / δ⌉₊ with hc
  set a : ℕ := ⌈t * (c + 1)⌉₊ with ha
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 fun h => by
    have := Nat.ceil_eq_zero.1 (ha ▸ h); nlinarith
  refine ⟨Nat.pair (a - 1) c, ?_⟩
  simp only [qT, Nat.unpair_pair]
  have e : ((a - 1 : ℕ) : ℝ) + 1 = a := by rw [Nat.cast_sub ha1]; push_cast; ring
  rw [e]
  have h1 : t * (c + 1) ≤ a := Nat.le_ceil _
  have h2 : (a : ℝ) < t * (c + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : 1 / δ ≤ c := Nat.le_ceil _
  have h4 : 1 ≤ δ * (c + 1) := by
    rw [div_le_iff₀ hδ] at h3; nlinarith
  rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, le_div_iff₀ hc1, div_le_iff₀ hc1]
  constructor <;> nlinarith

/-- A sequence of times of the dense set converging to `t > 0`. -/
theorem exists_seq_qT {t : ℝ} (ht : 0 < t) :
    ∃ js : ℕ → ℕ, Tendsto (fun k => qT (js k)) atTop (𝓝 t) := by
  choose js hjs using fun k : ℕ => exists_qT_near ht (Nat.one_div_pos_of_nat (n := k))
  refine ⟨js, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => (hjs k)) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-!
## Laws of the paths on the dense set
-/

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℝ → Ωs n → St}

/-- `ω ↦ (X n (qT j) ω)_j`. -/
def pathY (X : ∀ n, ℝ → Ωs n → St) (n : ℕ) (ω : Ωs n) : ℕ → St := fun j => X n (qT j) ω

/-- A.e.-measurable marginals at positive times. -/
def AEMeas (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℝ → Ωs n → St) : Prop :=
  ∀ n t, 0 < t → AEMeasurable (X n t) (Ps n)

theorem aemeasurable_pathY (hX : AEMeas Ps X) (n : ℕ) : AEMeasurable (pathY X n) (Ps n) :=
  AEMeasurable.of_eval fun j => hX n _ (qT_pos j)

/-- The law of the path on the dense time set. -/
def lawY (Ps : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (Ps n)]
    (X : ∀ n, ℝ → Ωs n → St) (n : ℕ) : ProbabilityMeasure (ℕ → St) :=
  ⟨(Ps n).map (pathY X n), inferInstance⟩

/-- **One-time tightness of the masses** (for `n` large). -/
def OneTimeTight (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℝ → Ωs n → St) : Prop :=
  ∀ t, 0 < t → ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (N : ℕ), ∀ n, N ≤ n →
    Ps n {ω | M < moment 0 (X n t ω)} ≤ ENNReal.ofReal θ

/-- For one `n`, the mass tail tends to `0`. -/
theorem exists_mass_bound_one [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X) {t : ℝ} (ht : 0 < t) (n : ℕ) {θ : ℝ}
    (hθ : 0 < θ) : ∃ m : ℕ, Ps n {ω | (m : ℝ) < moment 0 (X n t ω)} ≤ ENNReal.ofReal θ := by
  have hf : AEMeasurable (fun ω => moment 0 (X n t ω)) (Ps n) :=
    (measurable_moment 0).comp_aemeasurable (hX n t ht)
  have hT := tendsto_measure_iInter_atTop (μ := Ps n)
    (s := fun m : ℕ => {ω | (m : ℝ) < moment 0 (X n t ω)})
    (fun m => nullMeasurableSet_lt aemeasurable_const hf)
    (fun m m' hmm' ω (hω : (m' : ℝ) < _) =>
      show (m : ℝ) < _ from lt_of_le_of_lt (Nat.cast_le.2 hmm') hω) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ m : ℕ, {ω | (m : ℝ) < moment 0 (X n t ω)}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨⌈moment 0 (X n t ω)⌉₊, Nat.le_ceil _⟩
  rw [he, measure_empty] at hT
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  exact ⟨m, hm.le⟩

/-- **One mass bound for all `n`.** -/
theorem exists_mass_bound [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X) (hT : OneTimeTight Ps X) {t : ℝ} (ht : 0 < t)
    {θ : ℝ} (hθ : 0 < θ) : ∃ M : ℝ, ∀ n, Ps n {ω | M < moment 0 (X n t ω)} ≤ ENNReal.ofReal θ := by
  obtain ⟨M₀, N, hN⟩ := hT t ht θ hθ
  choose ms hms using fun n => exists_mass_bound_one hX ht n hθ
  refine ⟨max M₀ (((Finset.range N).sup ms : ℕ) : ℝ), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · refine le_trans (measure_mono fun ω hω => ?_) (hms n)
    have : (ms n : ℝ) ≤ (((Finset.range N).sup ms : ℕ) : ℝ) := by
      exact_mod_cast Finset.le_sup (f := ms) (Finset.mem_range.2 hn)
    exact show (ms n : ℝ) < _ from lt_of_le_of_lt (this.trans (le_max_right _ _)) hω
  · refine le_trans (measure_mono fun ω (hω : max M₀ _ < moment 0 (X n t ω)) => ?_) (hN n hn)
    exact show M₀ < _ from lt_of_le_of_lt (le_max_left _ _) hω

theorem moment_zero_eq_mass (ν : St) : moment 0 ν = (ν.mass : ℝ) := by
  rw [← real_univ_eq_moment_zero]
  simp [measureReal_def, ← FiniteMeasure.ennreal_mass]

/-- **The path laws are tight.** -/
theorem isTight_lawY [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X) (hT : OneTimeTight Ps X) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (ℕ → St)) : Measure (ℕ → St)) |
      μ ∈ range (lawY Ps X)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨θ, hθ, hθε⟩ : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, by rw [ENNReal.ofReal_toReal hne]⟩
  choose M hM using fun j : ℕ => exists_mass_bound hX hT (qT_pos j)
    (θ := θ / 2 / 2 ^ j) (by positivity)
  let K : Set (ℕ → St) := Set.univ.pi fun j => {ν : St | ν.mass ≤ Real.toNNReal (M j)}
  refine ⟨K, isCompact_univ_pi fun j =>
    isCompact_setOfPred_finiteMeasure_le_of_compactSpace unitInterval _, ?_⟩
  rintro _ ⟨μ, ⟨n, rfl⟩, rfl⟩
  have hsub : Kᶜ ⊆ ⋃ j, {ω : ℕ → St | M j < moment 0 (ω j)} := by
    intro ω hω
    simp only [K, mem_compl_iff, mem_univ_pi, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨j, hj⟩ := hω
    refine mem_iUnion.2 ⟨j, ?_⟩
    rw [mem_ofPred_eq, moment_zero_eq_mass]
    have h' : ((Real.toNNReal (M j) : ℝ≥0) : ℝ) < (ω j).mass := by exact_mod_cast hj
    exact lt_of_le_of_lt (Real.le_coe_toNNReal (M j)) h'
  have hmeas : ∀ j, MeasurableSet {ω : ℕ → St | M j < moment 0 (ω j)} := fun j =>
    measurableSet_lt measurable_const ((measurable_moment 0).comp (measurable_pi_apply j))
  calc ((lawY Ps X n : ProbabilityMeasure (ℕ → St)) : Measure (ℕ → St)) Kᶜ
      ≤ ∑' j, ((Ps n).map (pathY X n)) {ω : ℕ → St | M j < moment 0 (ω j)} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ = ∑' j, Ps n {ω | M j < moment 0 (X n (qT j) ω)} := by
        congr 1; funext j
        rw [Measure.map_apply_of_aemeasurable (aemeasurable_pathY hX n) (hmeas j)]
        rfl
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (θ / 2 / 2 ^ j) := ENNReal.tsum_le_tsum fun j => hM j n
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_two' θ)), tsum_geometric_two']
    _ ≤ ε := hθε

/-- **Prokhorov extraction**: a strictly increasing `ms` and a limit law `Q` on `ℕ → FM[0,1]`. -/
theorem exists_tendsto_lawY [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X) (hT : OneTimeTight Ps X) :
    ∃ (Q : ProbabilityMeasure (ℕ → St)) (ms : ℕ → ℕ), StrictMono ms ∧
      Tendsto (fun n => lawY Ps X (ms n)) atTop (𝓝 Q) := by
  have hc := isCompact_closure_of_isTightMeasureSet (isTight_lawY hX hT)
  obtain ⟨Q, -, ms, hms, hlim⟩ := hc.tendsto_subseq (x := lawY Ps X)
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨Q, ms, hms, hlim⟩

end BlockBand.Transmission.LawDuality.SubLimit
