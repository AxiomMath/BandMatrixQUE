module

public import BlockBand.SourceProcess.CapCond.Sides

/-!
# The physical cap probability converges to the entrance cap probability

* `eventually_capProb_le` (every `h`): `limsup_W P_W(A_W) ≤ P(μ(s) ∈ capSet K h)`;
* `eventually_le_capProb` (`h > 0`): `liminf_W P_W(A_W) ≥ P(t_K(μ(s)) < h²)`;
* `tendsto_capProb`: if `P(t_K(μ(s)) = h²) = 0`, then `P_W(A_W) → P(μ(s) ∈ capSet K h)`.

The proof feeds `capTest` to `IsTransmissionLimit.fdd` at the single time `s`,
with the thresholds `h² < x` (upper side) or `x < h²` (lower side), and lets `x → h²` by
continuity of the entrance law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent
open scoped ENNReal

theorem isFiniteMeasure_entranceLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (μ : ℝ → Ω → FiniteMeasure unitInterval) (s : ℝ) :
    IsFiniteMeasure (entranceLaw P μ s) := by
  unfold entranceLaw; infer_instance

/-- Continuity from above at `h²`. -/
theorem tendsto_ent_above (ρ : Measure (Measure unitInterval)) [IsFiniteMeasure ρ] (K : ℕ)
    (h : ℝ) : Tendsto (fun n : ℕ => (ρ {ν | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)}).toReal)
      atTop (𝓝 (ρ (capSet K h)).toReal) := by
  have ht := tendsto_measure_iInter_atTop (μ := ρ)
    (s := fun n : ℕ => {ν | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)})
    (fun n => (measurableSet_extract_lt K _).nullMeasurableSet) (fun n m hnm ν hν => by
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      change seqExtract ν K < _ at hν ⊢
      linarith) ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ n : ℕ, {ν : Measure unitInterval | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)}) =
      capSet K h := by
    ext ν
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, capSet]
    constructor
    · intro hν
      by_contra hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hc))
      linarith [hν n]
    · intro hν n
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hI] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

/-- Continuity from below at `h²`. -/
theorem tendsto_ent_below (ρ : Measure (Measure unitInterval)) [IsFiniteMeasure ρ] (K : ℕ)
    (h : ℝ) : Tendsto (fun n : ℕ => (ρ {ν | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)}).toReal)
      atTop (𝓝 (ρ {ν | seqExtract ν K < h ^ 2}).toReal) := by
  have ht := tendsto_measure_iUnion_atTop (μ := ρ)
    (s := fun n : ℕ => {ν | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)}) (fun n m hnm ν hν => by
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      change seqExtract ν K < _ at hν ⊢
      linarith)
  have hU : (⋃ n : ℕ, {ν : Measure unitInterval | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)}) =
      {ν | seqExtract ν K < h ^ 2} := by
    ext ν
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hν
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hν)
      exact ⟨n, by linarith⟩
  rw [hU] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E : ℝ}

/-- **Upper side**: eventually `P_W(A_W) ≤ P(μ(s) ∈ capSet K h) + ε` (every `h`, every `K`). -/
theorem eventually_capProb_le (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ}
    (hs : 0 < s) (h : ℝ) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ W in atTop, (growthPathLaw W b (physCapEvent b E s h K W)).toReal ≤
      (entranceLaw P μ s (capSet K h)).toReal + ε := by
  have := hlim.prob
  have := isFiniteMeasure_entranceLaw P μ s
  have hμ := hlim.measurable s hs
  have hA := SourcePins.entranceAtomic_of hTL b hb0 hb E hE1 hE2 Ω _ P μ hlim s hs
  obtain ⟨n, hn⟩ := ((tendsto_ent_above (entranceLaw P μ s) K h).eventually
    (gt_mem_nhds (show (entranceLaw P μ s (capSet K h)).toReal <
      (entranceLaw P μ s (capSet K h)).toReal + ε / 2 by linarith))).exists
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have ha : 0 < (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 := by positivity
  have hac : (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 < h ^ 2 + 1 / ((n : ℝ) + 1) := by linarith
  have hha : h ^ 2 < (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 := by linarith
  have hconv := hlim.fdd 1 (fun _ => s) (fun _ => hs) (capTest _ (h ^ 2 + 1 / ((n : ℝ) + 1)) ha K)
  have hle := integral_capTest_le hμ hA ha hac K
  filter_upwards [hconv.eventually (gt_mem_nhds (lt_add_of_pos_right
    (∫ ω, capTest _ (h ^ 2 + 1 / ((n : ℝ) + 1)) ha K (fun _ => μ s ω) ∂P) (half_pos hε))),
    eventually_ge_atTop 1]
    with W hW hW1
  have := capProb_le_integral (s := s) hb hE1 hE2 hW1 ha hac hha K
  linarith

/-- **Lower side**: eventually `P(t_K(μ(s)) < h²) - ε ≤ P_W(A_W)` (`h > 0`). -/
theorem eventually_le_capProb (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ}
    (hs : 0 < s) {h : ℝ} (hh : 0 < h) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ W in atTop, (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal - ε ≤
      (growthPathLaw W b (physCapEvent b E s h K W)).toReal := by
  have := hlim.prob
  have := isFiniteMeasure_entranceLaw P μ s
  have hμ := hlim.measurable s hs
  have hA := SourcePins.entranceAtomic_of hTL b hb0 hb E hE1 hE2 Ω _ P μ hlim s hs
  have hh2 : 0 < h ^ 2 := by positivity
  obtain ⟨n, hn, hn'⟩ := (((tendsto_ent_below (entranceLaw P μ s) K h).eventually
    (lt_mem_nhds (show (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal - ε / 2 <
      (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal by linarith))).and
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hh2))).exists
  have ha : 0 < h ^ 2 - 1 / ((n : ℝ) + 1) := by linarith
  have hac : h ^ 2 - 1 / ((n : ℝ) + 1) < h ^ 2 := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hconv := hlim.fdd 1 (fun _ => s) (fun _ => hs) (capTest _ (h ^ 2) ha K)
  have hle := le_integral_capTest hμ hA ha hac K
  filter_upwards [hconv.eventually (lt_mem_nhds (sub_lt_self
    (∫ ω, capTest _ (h ^ 2) ha K (fun _ => μ s ω) ∂P) (half_pos hε))), eventually_ge_atTop 1]
    with W hW hW1
  have := integral_le_capProb (s := s) hb hE1 hE2 hW1 ha hac le_rfl K
  linarith

/-- Without an atom of `t_K(μ(s))` at `h²`, `P(t_K(μ(s)) < h²) = P(μ(s) ∈ capSet K h)`. -/
theorem ent_lt_eq_capSet (ρ : Measure (Measure unitInterval)) (K : ℕ) (h : ℝ)
    (h0 : ρ {ν | seqExtract ν K = h ^ 2} = 0) :
    ρ {ν | seqExtract ν K < h ^ 2} = ρ (capSet K h) := by
  refine le_antisymm (measure_mono fun ν (hν : seqExtract ν K < h ^ 2) => (le_of_lt hν : seqExtract ν K ≤ h ^ 2)) ?_
  calc ρ (capSet K h) ≤ ρ ({ν | seqExtract ν K < h ^ 2} ∪ {ν | seqExtract ν K = h ^ 2}) :=
        measure_mono fun ν (hν : seqExtract ν K ≤ h ^ 2) => (lt_or_eq_of_le hν).imp id id
    _ ≤ _ := (measure_union_le _ _).trans (by rw [h0, add_zero])

/-- **Convergence of the cap probability** off the atoms at `h²`. -/
theorem tendsto_capProb (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ}
    (hs : 0 < s) {h : ℝ} (hh : 0 < h) (K : ℕ)
    (h0 : entranceLaw P μ s {ν | seqExtract ν K = h ^ 2} = 0) :
    Tendsto (fun W => (growthPathLaw W b (physCapEvent b E s h K W)).toReal) atTop
      (𝓝 (entranceLaw P μ s (capSet K h)).toReal) := by
  have e := ent_lt_eq_capSet (entranceLaw P μ s) K h h0
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  · filter_upwards [eventually_le_capProb hTL hb0 hb hE1 hE2 hlim hs hh K
      (half_pos (sub_pos.2 hx))] with W hW
    rw [e] at hW
    linarith
  · filter_upwards [eventually_capProb_le hTL hb0 hb hE1 hE2 hlim hs h K
      (half_pos (sub_pos.2 hx))] with W hW
    linarith

end BlockBand.SourceProcess.CapCond
