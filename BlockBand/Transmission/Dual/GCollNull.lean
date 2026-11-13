module

public import BlockBand.Transmission.Dual.GLemmaCSeq

/-!
# Collisions at positive height are null

`gapSet q η K δ ⊆ ℝ^{2q}` is the closed set
`{x_i + y_j ≥ η ∀ i j, x_i ≤ K ∀ i, some x-gap or y-gap ≤ δ}`. `collSet η K` is the event (on
`ℕ → CPath`) that for **every** `δ = 1/(m+1)` the stop sequence enters `gapSet η K δ` before
some truncated exit. **`measure_collSet`**: under the law of the stop sequence of the dual up to
exhaustion this event is null (`lemmaC_seq` with `M = C δ`, `δ → 0`; the start `z ∉ gapSet δ`
once `δ` is below the gaps of `z`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}

/-- The closed gap set `{x_i + y_j ≥ η, x_i ≤ K, some x-gap or y-gap ≤ δ}`. -/
def gapSet (q : ℕ) (η K δ : ℝ) : Set (Fin (q + q) → ℝ) :=
  {w | (∀ i j, η ≤ (ofFlat q w).1 i + (ofFlat q w).2 j) ∧ (∀ i, (ofFlat q w).1 i ≤ K) ∧
    ((∃ i k, i < k ∧ (ofFlat q w).1 k - (ofFlat q w).1 i ≤ δ) ∨
      (∃ i k, i < k ∧ (ofFlat q w).2 k - (ofFlat q w).2 i ≤ δ))}

theorem isClosed_gapSet (q : ℕ) (η K δ : ℝ) : IsClosed (gapSet q η K δ) := by
  have c1 : ∀ i, Continuous fun w : Fin (q + q) → ℝ => (ofFlat q w).1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp (ofFlat q).continuous)
  have c2 : ∀ j, Continuous fun w : Fin (q + q) → ℝ => (ofFlat q w).2 j := fun j =>
    (continuous_apply j).comp (continuous_snd.comp (ofFlat q).continuous)
  simp only [gapSet, ofPred_and, ofPred_forall, ofPred_or]
  refine (isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le continuous_const ((c1 i).add (c2 j))).inter
    ((isClosed_iInter fun i => isClosed_le (c1 i) continuous_const).inter ?_)
  refine IsClosed.union ?_ ?_
  · simp only [ofPred_exists]
    refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun k => ?_
    by_cases hik : i < k
    · simp only [hik, true_and]; exact isClosed_le ((c1 k).sub (c1 i)) continuous_const
    · simp only [hik, false_and, ofPred_false]; exact isClosed_empty
  · simp only [ofPred_exists]
    refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun k => ?_
    by_cases hik : i < k
    · simp only [hik, true_and]; exact isClosed_le ((c2 k).sub (c2 i)) continuous_const
    · simp only [hik, false_and, ofPred_false]; exact isClosed_empty

/-- A chamber point is outside the gap sets of small `δ`. -/
theorem eventually_notMem_gapSet {z : Fin (q + q) → ℝ} (hz : z ∈ flatChamber q) (η K : ℝ) :
    ∀ᶠ m : ℕ in atTop, z ∉ gapSet q η K (1 / ((m : ℝ) + 1)) := by
  have ht : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx : ∀ i k : Fin q, i < k → ∀ᶠ m : ℕ in atTop,
      1 / ((m : ℝ) + 1) < (ofFlat q z).1 k - (ofFlat q z).1 i := fun i k hik =>
    ht.eventually (gt_mem_nhds (sub_pos.2 (hz.1 hik)))
  have hy : ∀ i k : Fin q, i < k → ∀ᶠ m : ℕ in atTop,
      1 / ((m : ℝ) + 1) < (ofFlat q z).2 k - (ofFlat q z).2 i := fun i k hik =>
    ht.eventually (gt_mem_nhds (sub_pos.2 (hz.2.1 hik)))
  have hx' := eventually_all.2 fun i => eventually_all.2 fun k =>
    (eventually_imp_distrib_left (p := i < k)).2 fun h => hx i k h
  have hy' := eventually_all.2 fun i => eventually_all.2 fun k =>
    (eventually_imp_distrib_left (p := i < k)).2 fun h => hy i k h
  filter_upwards [hx', hy'] with m hmx hmy hmem
  rcases hmem.2.2 with ⟨i, k, hik, h⟩ | ⟨i, k, hik, h⟩
  · exact absurd h (not_le.2 (hmx i k hik))
  · exact absurd h (not_le.2 (hmy i k hik))

/-- The event "collision at positive height `≥ η`, below height `K`". -/
def collSet (W : ℕ → Set (Fin (q + q) → ℝ)) (t₀ : ℝ≥0) (η K : ℝ) : Set (ℕ → CPath (q + q)) :=
  ⋂ m : ℕ, ⋃ n, hitSet W t₀ (gapSet q η K (1 / ((m : ℝ) + 1))) n

/-- **Collisions at positive height are null** under the law of the stop sequence. -/
theorem measure_collSet (hD0 : 0 < D0) {z : Fin (q + q) → ℝ} {W : ℕ → Set (Fin (q + q) → ℝ)}
    (hW : ∀ n, IsInteriorDomain (W n) (flatChamber q)) (hmono : Monotone W) (hz : z ∈ W 0)
    (F : B1Family D0 q z) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (t₀ : ℝ≥0) {η : ℝ} (hη : 0 < η)
    (K : ℝ) : (Pq q).map (F.stopSeq W t₀ r) (collSet W t₀ η K) = 0 := by
  have hz' : z ∈ flatChamber q := (hW 0).2.2 (subset_closure hz)
  obtain ⟨C, hC⟩ := exists_cauchyH_le_of_gap q hη K
  set c : ℝ := max C 0
  have hb : ∀ᶠ m : ℕ in atTop, (Pq q).map (F.stopSeq W t₀ r) (collSet W t₀ η K) ≤
      ENNReal.ofReal (c * (1 / ((m : ℝ) + 1)) / flatH q z) := by
    filter_upwards [eventually_notMem_gapSet hz' η K] with m hm
    refine (measure_mono (iInter_subset _ m)).trans ?_
    have hδ : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    refine lemmaC_seq hD0 hW hmono hz F hr hball t₀ (isClosed_gapSet q η K _) hm
      (mul_nonneg (le_max_right _ _) hδ) fun w hw => ?_
    obtain ⟨h1, h2, h3⟩ := hw.1
    exact (hC _ hw.2 h1 h2 _ h3).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)
  have ht : Tendsto (fun m : ℕ => ENNReal.ofReal (c * (1 / ((m : ℝ) + 1)) / flatH q z)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (h0.const_mul c).div_const (flatH q z)
    simpa using this
  exact le_antisymm (ge_of_tendsto ht hb) bot_le

end BlockBand.Transmission.Dual.G
