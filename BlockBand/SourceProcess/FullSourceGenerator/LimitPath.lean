module

public import BlockBand.SourceProcess.FullSourceGenerator.LimitTight

/-!
# Continuous versions of the limit paths

* `goodSet t₀`: for every word, uniformly continuous on the dense times of every `[t₀, t₀+m]`;
* `extPath t₀ a ω t`: the limit along dense times `→ t` (`0` off `goodSet`); measurable in `ω`
  (`measurable_extPath`), continuous on `[t₀, ∞)` (`continuousOn_extPath`), equal to the path
  at the dense times (`extPath_dT`);
* `Modulus`: the sup-modulus of `X n a` on `[t₀, T]`, for `n` large; **`ae_goodSet`**: every
  limit law of the paths charges only `goodSet` (portmanteau for the open bad sets).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.WordLim

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable (t₀ : ℝ)

/-- Paths whose word coordinates are uniformly continuous on the dense times of `[t₀, t₀+m]`. -/
def goodSet : Set (ℕ → ℂ) :=
  {ω | ∀ a m e : ℕ, ∃ d : ℕ, ∀ j j' : ℕ,
    (dT t₀ j ≤ t₀ + m ∧ dT t₀ j' ≤ t₀ + m ∧ |dT t₀ j - dT t₀ j'| ≤ 1 / ((d : ℝ) + 1)) →
      ‖ω (Nat.pair a j) - ω (Nat.pair a j')‖ ≤ 1 / ((e : ℝ) + 1)}

theorem measurableSet_goodSet : MeasurableSet (goodSet t₀) := by
  simp only [goodSet, ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun m => MeasurableSet.iInter
    fun e => MeasurableSet.iUnion fun d => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun j' => MeasurableSet.iInter fun _ => measurableSet_le (((measurable_pi_apply
      (Nat.pair a j)).sub (measurable_pi_apply (Nat.pair a j'))).norm) measurable_const

variable {t₀}

theorem local_mod {ω : ℕ → ℂ} (hω : ω ∈ goodSet t₀) {t : ℝ} (_ht : t₀ ≤ t) (a : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ > 0, ∀ j j', |dT t₀ j - t| < ρ → |dT t₀ j' - t| < ρ →
      ‖ω (Nat.pair a j) - ω (Nat.pair a j')‖ < ε := by
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  set m : ℕ := ⌈t - t₀⌉₊ + 1
  have hm : t + 1 ≤ t₀ + m := by
    have := Nat.le_ceil (t - t₀); simp only [m]; push_cast; linarith
  obtain ⟨d, hd⟩ := hω a m e
  refine ⟨min 1 (1 / (2 * ((d : ℝ) + 1))), by positivity, fun j j' hj hj' => ?_⟩
  have hw : ∀ s, |s - t| < min 1 (1 / (2 * ((d : ℝ) + 1))) → s ≤ t₀ + m := fun s hs => by
    have := (lt_min_iff.1 hs).1; rw [abs_lt] at this; linarith
  refine lt_of_le_of_lt (hd j j' ⟨hw _ hj, hw _ hj', ?_⟩) he
  have h1 := (lt_min_iff.1 hj).2
  have h2 := (lt_min_iff.1 hj').2
  have : |dT t₀ j - dT t₀ j'| ≤ |dT t₀ j - t| + |dT t₀ j' - t| := by
    rw [abs_sub_comm (dT t₀ j') t]; exact abs_sub_le _ _ _
  have e2 : 1 / (2 * ((d : ℝ) + 1)) + 1 / (2 * ((d : ℝ) + 1)) = 1 / ((d : ℝ) + 1) := by
    field_simp; ring
  linarith

theorem eventually_near {u : ℕ → ℕ} {t : ℝ} (hu : Tendsto (fun k => dT t₀ (u k)) atTop (𝓝 t))
    {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ k in atTop, |dT t₀ (u k) - t| < ρ := by
  have := (Metric.tendsto_nhds.1 hu) ρ hρ
  simpa [Real.dist_eq] using this

theorem exists_lim {ω : ℕ → ℂ} (hω : ω ∈ goodSet t₀) {t : ℝ} (ht : t₀ ≤ t) (a : ℕ) {u : ℕ → ℕ}
    (hu : Tendsto (fun k => dT t₀ (u k)) atTop (𝓝 t)) :
    ∃ z : ℂ, Tendsto (fun k => ω (Nat.pair a (u k))) atTop (𝓝 z) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨ρ, hρ, hρm⟩ := local_mod hω ht a hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_near hu hρ)
  exact ⟨N, fun n hn => by rw [dist_eq_norm]; exact hρm _ _ (hN n hn) (hN N le_rfl)⟩

variable (t₀) in
/-- A fixed dense-time sequence converging to `t ≥ t₀`. -/
def seqT (t : ℝ) : ℕ → ℕ :=
  if h : t₀ ≤ t then Classical.choose (exists_seq_dT t₀ h) else fun _ => 0

theorem tendsto_seqT {t : ℝ} (ht : t₀ ≤ t) :
    Tendsto (fun k => dT t₀ (seqT t₀ t k)) atTop (𝓝 t) := by
  rw [seqT, dite_eq_left ht]; exact Classical.choose_spec (exists_seq_dT t₀ ht)

variable (t₀) in
open scoped Classical in
/-- **The continuous extension** of word `a` of a good path (`0` off `goodSet`). -/
def extPath (a : ℕ) (ω : ℕ → ℂ) (t : ℝ) : ℂ :=
  if ω ∈ goodSet t₀ then limUnder atTop (fun k => ω (Nat.pair a (seqT t₀ t k))) else 0

theorem tendsto_extPath {ω : ℕ → ℂ} (hω : ω ∈ goodSet t₀) (a : ℕ) {t : ℝ} (ht : t₀ ≤ t) :
    Tendsto (fun k => ω (Nat.pair a (seqT t₀ t k))) atTop (𝓝 (extPath t₀ a ω t)) := by
  rw [extPath, ite_eq_left hω]
  exact tendsto_nhds_limUnder (exists_lim hω ht a (tendsto_seqT ht))

theorem extPath_dT {ω : ℕ → ℂ} (hω : ω ∈ goodSet t₀) (a j : ℕ) :
    extPath t₀ a ω (dT t₀ j) = ω (Nat.pair a j) := by
  refine tendsto_nhds_unique (tendsto_extPath hω a (le_dT t₀ j)) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hρm⟩ := local_mod hω (le_dT t₀ j) a hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_near (tendsto_seqT (le_dT t₀ j)) hρ)
  exact ⟨N, fun n hn => by rw [dist_eq_norm]; exact hρm _ _ (hN n hn) (by simpa using hρ)⟩

/-- **Continuity of the extension on `[t₀, ∞)`.** -/
theorem continuousOn_extPath {ω : ℕ → ℂ} (hω : ω ∈ goodSet t₀) (a : ℕ) :
    ContinuousOn (extPath t₀ a ω) (Ici t₀) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨ρ, hρ, hρm⟩ := local_mod hω ht a (half_pos hε)
  refine ⟨ρ / 2, half_pos hρ, fun s hs hst => ?_⟩
  rw [Real.dist_eq] at hst
  rw [dist_eq_norm]
  have hlim := ((tendsto_extPath hω a hs).sub (tendsto_extPath hω a ht)).norm
  have hev : ∀ᶠ k in atTop, ‖ω (Nat.pair a (seqT t₀ s k)) - ω (Nat.pair a (seqT t₀ t k))‖ ≤
      ε / 2 := by
    filter_upwards [eventually_near (tendsto_seqT hs) (half_pos hρ),
      eventually_near (tendsto_seqT ht) hρ] with k hk1 hk2
    refine (hρm _ _ ?_ hk2).le
    have := abs_sub_le (dT t₀ (seqT t₀ s k)) s t
    linarith
  exact lt_of_le_of_lt (le_of_tendsto hlim hev) (half_lt_self hε)

theorem measurable_extPath (a : ℕ) {t : ℝ} (ht : t₀ ≤ t) :
    Measurable fun ω : ℕ → ℂ => extPath t₀ a ω t := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun k => (goodSet t₀).piecewise
    (fun ω : ℕ → ℂ => ω (Nat.pair a (seqT t₀ t k))) (fun _ => 0)) (fun k => ?_)
    (tendsto_pi_nhds.2 fun ω => ?_)
  · exact Measurable.piecewise (measurableSet_goodSet t₀) (measurable_pi_apply _) measurable_const
  · by_cases hω : ω ∈ goodSet t₀
    · simpa only [Set.piecewise_eq_of_mem _ _ _ hω] using tendsto_extPath hω a ht
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hω, extPath, ite_eq_right hω]
      exact tendsto_const_nhds

/-!
## The limit law charges only good paths
-/

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℕ → ℝ → Ωs n → ℂ}

variable (t₀) in
/-- **The sup-modulus on `[t₀, T]`** (for `n` large). -/
def Modulus (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℕ → ℝ → Ωs n → ℂ) : Prop :=
  ∀ (a : ℕ) (T η θ : ℝ), 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    Ps n {ω | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ δ ∧ η < ‖X n a t ω - X n a t' ω‖} ≤
      ENNReal.ofReal θ

variable (t₀) in
/-- The bad set at scale `δ`. -/
def badSet (a m e d : ℕ) : Set (ℕ → ℂ) :=
  {ω | ∃ j j' : ℕ, (dT t₀ j ≤ t₀ + m ∧ dT t₀ j' ≤ t₀ + m ∧
    |dT t₀ j - dT t₀ j'| ≤ 1 / ((d : ℝ) + 1)) ∧
    1 / ((e : ℝ) + 1) < ‖ω (Nat.pair a j) - ω (Nat.pair a j')‖}

theorem isOpen_badSet (a m e d : ℕ) : IsOpen (badSet t₀ a m e d) := by
  simp only [badSet, ofPred_exists]
  refine isOpen_iUnion fun j => isOpen_iUnion fun j' => ?_
  by_cases hp : dT t₀ j ≤ t₀ + m ∧ dT t₀ j' ≤ t₀ + m ∧ |dT t₀ j - dT t₀ j'| ≤ 1 / ((d : ℝ) + 1)
  · simp only [hp, true_and]
    exact isOpen_lt continuous_const (((continuous_apply (Nat.pair a j)).sub
      (continuous_apply (Nat.pair a j'))).norm)
  · have he : {x : ℕ → ℂ | (dT t₀ j ≤ t₀ + m ∧ dT t₀ j' ≤ t₀ + m ∧
        |dT t₀ j - dT t₀ j'| ≤ 1 / ((d : ℝ) + 1)) ∧
        1 / ((e : ℝ) + 1) < ‖x (Nat.pair a j) - x (Nat.pair a j')‖} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hp hx.1
    rw [he]; exact isOpen_empty

theorem compl_goodSet_subset : (goodSet t₀)ᶜ ⊆ ⋃ a, ⋃ m, ⋃ e, ⋂ d, badSet t₀ a m e d := by
  intro ω hω
  simp only [goodSet, mem_compl_iff, mem_ofPred_eq, not_forall, not_exists, not_le,
    exists_prop] at hω
  obtain ⟨a, m, e, h⟩ := hω
  simp only [mem_iUnion, mem_iInter]
  exact ⟨a, m, e, fun d => by obtain ⟨j, j', hj, hlt⟩ := h d; exact ⟨j, j', hj, hlt⟩⟩

/-- **Every limit law of the paths charges only `goodSet`.** -/
theorem ae_goodSet [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas t₀ Ps X)
    (hM : Modulus t₀ Ps X) {Q : ProbabilityMeasure (ℕ → ℂ)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY t₀ Ps X (ms n)) atTop (𝓝 Q)) :
    (Q : Measure (ℕ → ℂ)) (goodSet t₀)ᶜ = 0 := by
  refine measure_mono_null compl_goodSet_subset (measure_iUnion_null fun a =>
    measure_iUnion_null fun m => measure_iUnion_null fun e => ?_)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun θ hθ _ => ?_) (by simp)
  rw [zero_add]
  obtain ⟨δ, hδ, N, hN⟩ := hM a (t₀ + m) (1 / ((e : ℝ) + 1)) θ (by positivity)
    (by exact_mod_cast hθ)
  obtain ⟨d, hd⟩ := exists_nat_one_div_lt hδ
  refine (measure_mono (iInter_subset _ d)).trans ?_
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ
    (isOpen_badSet a m e d)).trans ?_
  refine liminf_le_of_frequently_le' (Eventually.frequently (eventually_atTop.2 ⟨N, fun n hn => ?_⟩))
  have hle : N ≤ ms n := hn.trans (hms.id_le n)
  show ((Ps (ms n)).map (pathY t₀ X (ms n))) (badSet t₀ a m e d) ≤ _
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_pathY hX _)
    (isOpen_badSet a m e d).measurableSet]
  refine (measure_mono fun ω hω => ?_).trans ((hN (ms n) hle).trans (by simp))
  obtain ⟨j, j', ⟨hj, hj', hjj⟩, hlt⟩ := hω
  refine ⟨dT t₀ j, ⟨le_dT t₀ j, hj⟩, dT t₀ j', ⟨le_dT t₀ j', hj'⟩, hjj.trans hd.le, ?_⟩
  simpa [pathY, Nat.unpair_pair] using hlt

end BlockBand.SourceProcess.FullSourceGenerator.WordLim
