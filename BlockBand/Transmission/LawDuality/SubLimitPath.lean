module

public import BlockBand.Transmission.LawDuality.SubLimitTight

/-!
# A continuous version of the limit on the dense time set

* `goodSet`: the paths whose moment paths `j ↦ m_i(ω_j)` are uniformly continuous on
  `{qT j ∈ [1/(m+1), m+1]}` for all `i, m` (rational moduli). `measurableSet_goodSet`.
* `local_mod`: on `goodSet`, near any `t > 0` the moments of `ω_j` oscillate little.
* `exists_lim`: on `goodSet`, `ω_{u_k}` converges in `FM[0,1]` whenever `qT (u k) → t > 0`
  (moments are Cauchy; masses bounded, so a cluster point exists in the compact
  `{mass ≤ C}`; moments determine weak limits, `tendsto_of_tendsto_moments`).
* `extPath ω t`: the limit along a fixed `qT`-sequence `seqT t → t` (and `0` off `goodSet`).
  `extPath_qT` (`= ω_j` at `t = qT j`), **`continuousOn_extPath`**, `measurable_extPath`.
* `MomentModulus` (the moment form of the `modulus` clause) and **`ae_goodSet`**: under it,
  every limit law `Q` of `lawY (ms n)` charges only `goodSet` (portmanteau for open sets).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality.SubLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

/-- The time window `[1/(m+1), m+1]`. -/
def Iw (m : ℕ) : Set ℝ := Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)

/-- Paths with uniformly continuous moment paths on every window. -/
def goodSet : Set (ℕ → St) :=
  {ω | ∀ i m η : ℕ, ∃ δ : ℕ, ∀ j j' : ℕ,
    (qT j ∈ Iw m ∧ qT j' ∈ Iw m ∧ |qT j - qT j'| ≤ 1 / ((δ : ℝ) + 1)) →
      |moment i (ω j) - moment i (ω j')| ≤ 1 / ((η : ℝ) + 1)}

theorem measurableSet_goodSet : MeasurableSet goodSet := by
  simp only [goodSet, ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun m => MeasurableSet.iInter
    fun η => MeasurableSet.iUnion fun δ => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun j' => MeasurableSet.iInter fun _ => measurableSet_le ?_ measurable_const
  exact (((measurable_moment i).comp (measurable_pi_apply j)).sub
    ((measurable_moment i).comp (measurable_pi_apply j'))).abs

/-- **Local modulus on `goodSet`.** -/
theorem local_mod {ω : ℕ → St} (hω : ω ∈ goodSet) {t : ℝ} (ht : 0 < t) (i : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ > 0, ∀ j j', |qT j - t| < ρ → |qT j' - t| < ρ →
      |moment i (ω j) - moment i (ω j')| < ε := by
  obtain ⟨η, hη⟩ := exists_nat_one_div_lt hε
  set m : ℕ := ⌈2 / t + 2 * t⌉₊
  have hm : 2 / t + 2 * t ≤ m := Nat.le_ceil _
  obtain ⟨δ, hδ⟩ := hω i m η
  refine ⟨min (t / 2) (1 / (2 * ((δ : ℝ) + 1))), by positivity, fun j j' hj hj' => ?_⟩
  have hw : ∀ s, |s - t| < min (t / 2) (1 / (2 * ((δ : ℝ) + 1))) → s ∈ Iw m := by
    intro s hs
    have h1 := (lt_min_iff.1 hs).1
    rw [abs_lt] at h1
    have h2 : 1 / ((m : ℝ) + 1) ≤ t / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 / t * t = 2 := by field_simp
      nlinarith
    have h3 : 0 < 2 / t := by positivity
    exact ⟨by linarith, by linarith⟩
  refine lt_of_le_of_lt (hδ j j' ⟨hw _ hj, hw _ hj', ?_⟩) hη
  have h1 := (lt_min_iff.1 hj).2
  have h2 := (lt_min_iff.1 hj').2
  have : |qT j - qT j'| ≤ |qT j - t| + |qT j' - t| := by
    rw [abs_sub_comm (qT j') t]; exact abs_sub_le _ _ _
  have e : 1 / (2 * ((δ : ℝ) + 1)) + 1 / (2 * ((δ : ℝ) + 1)) = 1 / ((δ : ℝ) + 1) := by
    field_simp; ring
  linarith

theorem eventually_near {u : ℕ → ℕ} {t : ℝ} (hu : Tendsto (fun k => qT (u k)) atTop (𝓝 t))
    {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ k in atTop, |qT (u k) - t| < ρ := by
  have := (Metric.tendsto_nhds.1 hu) ρ hρ
  simpa [Real.dist_eq] using this

/-- **Limits exist on `goodSet`.** -/
theorem exists_lim {ω : ℕ → St} (hω : ω ∈ goodSet) {t : ℝ} (ht : 0 < t) {u : ℕ → ℕ}
    (hu : Tendsto (fun k => qT (u k)) atTop (𝓝 t)) :
    ∃ ν : St, Tendsto (fun k => ω (u k)) atTop (𝓝 ν) := by
  have hc : ∀ i, CauchySeq fun k => moment i (ω (u k)) := by
    intro i
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨ρ, hρ, hρm⟩ := local_mod hω ht i hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_near hu hρ)
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hρm _ _ (hN n hn) (hN N le_rfl)⟩
  choose a ha using fun i => cauchySeq_tendsto_of_complete (hc i)
  let K : Set St := {ν | ν.mass ≤ Real.toNNReal (a 0 + 1)}
  have hK : IsCompact K := isCompact_setOfPred_finiteMeasure_le_of_compactSpace unitInterval _
  have hfr : ∃ᶠ k in atTop, ω (u k) ∈ K := by
    refine (((ha 0).eventually (gt_mem_nhds (lt_add_one (a 0)))).mono fun k hk => ?_).frequently
    show (ω (u k)).mass ≤ _
    rw [moment_zero_eq_mass] at hk
    have h0 : 0 ≤ a 0 + 1 := le_trans (by positivity) hk.le
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0]
    exact hk.le
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hK.tendsto_subseq' hfr
  have hmom : ∀ i, a i = moment i ν := fun i =>
    tendsto_nhds_unique ((ha i).comp hφ.tendsto_atTop)
      (((continuous_moment i).tendsto ν).comp hlim)
  exact ⟨ν, tendsto_of_tendsto_moments fun i => (hmom i) ▸ ha i⟩

/-- A fixed `qT`-sequence converging to `t` (`t > 0`). -/
def seqT (t : ℝ) : ℕ → ℕ :=
  if h : 0 < t then Classical.choose (exists_seq_qT h) else fun _ => 0

theorem tendsto_seqT {t : ℝ} (ht : 0 < t) : Tendsto (fun k => qT (seqT t k)) atTop (𝓝 t) := by
  rw [seqT, dite_eq_left ht]; exact Classical.choose_spec (exists_seq_qT ht)

open scoped Classical in
/-- **The continuous extension** of a good path (`0` off `goodSet`). -/
def extPath (ω : ℕ → St) (t : ℝ) : St :=
  if ω ∈ goodSet then limUnder atTop (fun k => ω (seqT t k)) else 0

theorem tendsto_extPath {ω : ℕ → St} (hω : ω ∈ goodSet) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => ω (seqT t k)) atTop (𝓝 (extPath ω t)) := by
  rw [extPath, ite_eq_left hω]
  exact tendsto_nhds_limUnder (exists_lim hω ht (tendsto_seqT ht))

theorem tendsto_moment_extPath {ω : ℕ → St} (hω : ω ∈ goodSet) {t : ℝ} (ht : 0 < t) (i : ℕ) :
    Tendsto (fun k => moment i (ω (seqT t k))) atTop (𝓝 (moment i (extPath ω t))) :=
  ((continuous_moment i).tendsto _).comp (tendsto_extPath hω ht)

/-- On `goodSet` the extension agrees with the path at the dense times. -/
theorem extPath_qT {ω : ℕ → St} (hω : ω ∈ goodSet) (j : ℕ) : extPath ω (qT j) = ω j := by
  refine tendsto_nhds_unique (tendsto_extPath hω (qT_pos j))
    (tendsto_of_tendsto_moments fun i => ?_)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hρm⟩ := local_mod hω (qT_pos j) i hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_near (tendsto_seqT (qT_pos j)) hρ)
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hρm _ _ (hN n hn) (by simpa using hρ)⟩

/-- **Continuity of the extension on `(0, ∞)`.** -/
theorem continuousOn_extPath {ω : ℕ → St} (hω : ω ∈ goodSet) :
    ContinuousOn (extPath ω) (Ioi 0) := by
  rw [isInducing_momentVec.continuousOn_iff, continuousOn_pi]
  intro i
  refine isOpen_Ioi.continuousOn_iff.2 fun t₀ (ht₀ : 0 < t₀) => ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρm⟩ := local_mod hω ht₀ i (half_pos hε)
  refine ⟨min (ρ / 2) (t₀ / 2), by positivity, fun t ht => ?_⟩
  rw [Real.dist_eq] at ht
  have ht1 := (lt_min_iff.1 ht).1
  have ht0 : 0 < t := by have := (lt_min_iff.1 ht).2; rw [abs_lt] at this; linarith
  show dist (moment i (extPath ω t)) (moment i (extPath ω t₀)) < ε
  rw [Real.dist_eq]
  have hlim := ((tendsto_moment_extPath hω ht0 i).sub (tendsto_moment_extPath hω ht₀ i)).abs
  have hev : ∀ᶠ k in atTop, |moment i (ω (seqT t k)) - moment i (ω (seqT t₀ k))| ≤ ε / 2 := by
    filter_upwards [eventually_near (tendsto_seqT ht0) (half_pos hρ),
      eventually_near (tendsto_seqT ht₀) hρ] with k hk1 hk2
    refine (hρm _ _ ?_ hk2).le
    have := abs_sub_le (qT (seqT t k)) t t₀
    linarith
  exact lt_of_le_of_lt (le_of_tendsto hlim hev) (half_lt_self hε)

theorem measurable_extPath {t : ℝ} (ht : 0 < t) : Measurable fun ω : ℕ → St => extPath ω t := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun k => goodSet.piecewise
    (fun ω : ℕ → St => ω (seqT t k)) (fun _ => 0)) (fun k => ?_) (tendsto_pi_nhds.2 fun ω => ?_)
  · exact Measurable.piecewise measurableSet_goodSet (measurable_pi_apply _) measurable_const
  · by_cases hω : ω ∈ goodSet
    · simpa only [Set.piecewise_eq_of_mem _ _ _ hω] using tendsto_extPath hω ht
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hω, extPath, ite_eq_right hω]
      exact tendsto_const_nhds

/-!
## The limit law charges only good paths
-/

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
  {X : ∀ n, ℝ → Ωs n → St}

/-- **The moment form of the `modulus` clause** (for `n` large). -/
def MomentModulus (Ps : ∀ n, Measure (Ωs n)) (X : ∀ n, ℝ → Ωs n → St) : Prop :=
  ∀ ε T : ℝ, 0 < ε → ∀ j : ℕ, ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
    ∀ n, N ≤ n → Ps n {ω | ∃ t ∈ Icc ε T, ∃ t' ∈ Icc ε T, |t - t'| ≤ δ ∧
      η < |moment j (X n t ω) - moment j (X n t' ω)|} ≤ ENNReal.ofReal θ

/-- The bad set at scale `δ`. -/
def badSet (i m η δ : ℕ) : Set (ℕ → St) :=
  {ω | ∃ j j' : ℕ, (qT j ∈ Iw m ∧ qT j' ∈ Iw m ∧ |qT j - qT j'| ≤ 1 / ((δ : ℝ) + 1)) ∧
    1 / ((η : ℝ) + 1) < |moment i (ω j) - moment i (ω j')|}

theorem isOpen_badSet (i m η δ : ℕ) : IsOpen (badSet i m η δ) := by
  simp only [badSet, ofPred_exists]
  refine isOpen_iUnion fun j => isOpen_iUnion fun j' => ?_
  by_cases hp : qT j ∈ Iw m ∧ qT j' ∈ Iw m ∧ |qT j - qT j'| ≤ 1 / ((δ : ℝ) + 1)
  · simp only [hp, true_and]
    exact isOpen_lt continuous_const ((((continuous_moment i).comp (continuous_apply j)).sub
      ((continuous_moment i).comp (continuous_apply j'))).abs)
  · have he : {x : ℕ → St | (qT j ∈ Iw m ∧ qT j' ∈ Iw m ∧ |qT j - qT j'| ≤ 1 / ((δ : ℝ) + 1)) ∧
        1 / ((η : ℝ) + 1) < |moment i (x j) - moment i (x j')|} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hp hx.1
    rw [he]; exact isOpen_empty

theorem compl_goodSet_subset : goodSetᶜ ⊆ ⋃ i, ⋃ m, ⋃ η, ⋂ δ, badSet i m η δ := by
  intro ω hω
  simp only [goodSet, mem_compl_iff, mem_ofPred_eq, not_forall, not_exists, not_le,
    exists_prop] at hω
  obtain ⟨i, m, η, h⟩ := hω
  simp only [mem_iUnion, mem_iInter]
  exact ⟨i, m, η, fun δ => by obtain ⟨j, j', hj, hlt⟩ := h δ; exact ⟨j, j', hj, hlt⟩⟩

/-- **Every limit law of the paths charges only `goodSet`.** -/
theorem ae_goodSet [∀ n, IsProbabilityMeasure (Ps n)] (hX : AEMeas Ps X)
    (hM : MomentModulus Ps X) {Q : ProbabilityMeasure (ℕ → St)} {ms : ℕ → ℕ}
    (hms : StrictMono ms) (hQ : Tendsto (fun n => lawY Ps X (ms n)) atTop (𝓝 Q)) :
    (Q : Measure (ℕ → St)) goodSetᶜ = 0 := by
  refine measure_mono_null compl_goodSet_subset (measure_iUnion_null fun i =>
    measure_iUnion_null fun m => measure_iUnion_null fun η => ?_)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun θ hθ _ => ?_) (by simp)
  rw [zero_add]
  obtain ⟨δ, hδ, N, hN⟩ := hM (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) (by positivity) i
    (1 / ((η : ℝ) + 1)) θ (by positivity) (by exact_mod_cast hθ)
  obtain ⟨δ', hδ'⟩ := exists_nat_one_div_lt hδ
  refine (measure_mono (iInter_subset _ δ')).trans ?_
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ (isOpen_badSet i m η δ')).trans ?_
  refine liminf_le_of_frequently_le' (Eventually.frequently (eventually_atTop.2 ⟨N, fun n hn => ?_⟩))
  have hle : N ≤ ms n := hn.trans (hms.id_le n)
  show ((Ps (ms n)).map (pathY X (ms n))) (badSet i m η δ') ≤ _
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_pathY hX _)
    (isOpen_badSet i m η δ').measurableSet]
  refine (measure_mono fun ω hω => ?_).trans ((hN (ms n) hle).trans (by simp))
  obtain ⟨j, j', ⟨hj, hj', hjj⟩, hlt⟩ := hω
  exact ⟨qT j, hj, qT j', hj', hjj.trans hδ'.le, hlt⟩

end BlockBand.Transmission.LawDuality.SubLimit
