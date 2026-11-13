module

public import BlockBand.Transmission.Dual.GSeqQ

/-!
# Positive-height collisions in the boundary classification: `Coll ⊆ ⋃_{η,K} collSet`

Level `q + 1`, `W` an exhaustion of `𝒞_{q+1}`.
* **`collLim_subset`** (pathwise): a nested sequence started in `W 0` whose left limit before
  `t₀` is a positive-height collision lies in `collSet W t₀ (1/(a+1)) b` for some `a, b ∈ ℕ`.
  Near `ρ_∞` the glued path is close to `z*`, so `x_i + y_j > η`, `x_i < K` and the colliding
  gap is `≤ δ` at times before some `ρ_n ∧ t₀`.
* **`measure_collLim`**: `collLim` is null under the law of the stop sequence of a `B1Family`
  (the collision bound over `η = 1/(a+1)`, `K = b`: `measure_collSet`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ} {t₀ : ℝ≥0} {W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}

theorem continuous_ofFlat_fst (i : Fin (q + 1)) :
    Continuous fun c : Fin ((q + 1) + (q + 1)) → ℝ => (ofFlat (q + 1) c).1 i :=
  (continuous_apply i).comp (continuous_fst.comp (ofFlat (q + 1)).continuous)

theorem continuous_ofFlat_snd (i : Fin (q + 1)) :
    Continuous fun c : Fin ((q + 1) + (q + 1)) → ℝ => (ofFlat (q + 1) c).2 i :=
  (continuous_apply i).comp (continuous_snd.comp (ofFlat (q + 1)).continuous)

/-- **`Coll ⊆ ⋃_{η,K} collSet`**, pathwise. -/
theorem collLim_subset {ŵ : ℕ → CPath ((q + 1) + (q + 1))} (h : IsNested W t₀ ŵ)
    (hE : IsExh W (flatChamber (q + 1))) (h0 : (ŵ 0).1 0 ∈ W 0) (hŵ : ŵ ∈ collLim q W t₀) :
    ∃ a b : ℕ, ŵ ∈ collSet W t₀ (1 / ((a : ℝ) + 1)) b := by
  obtain ⟨hlt, hl, hp⟩ := hŵ
  obtain ⟨c, hL⟩ := mem_llSet_iff.1 hl
  rw [hL.zstar_eq] at hp
  have hstrict := h.srho_lt_sinf hE h0 hlt
  have hT := (h.tendsto_sglue_iff hE.isOpen hE.mono hstrict c).2 hL
  obtain ⟨hmx, hmy⟩ := mono_of_mem_closure (h.LL_mem_closure hE h0 hlt hL)
  set C := ofFlat (q + 1) c with hC
  obtain ⟨a, ha⟩ := exists_nat_one_div_lt hp.1
  obtain ⟨b, hb⟩ := exists_nat_gt (∑ i, |C.1 i|)
  have hCb : ∀ i, C.1 i < b := fun i =>
    (le_abs_self _).trans_lt (((Finset.single_le_sum (fun k _ => abs_nonneg (C.1 k))
      (Finset.mem_univ i))).trans_lt hb)
  refine ⟨a, b, mem_iInter.2 fun m => ?_⟩
  set δ : ℝ := 1 / ((m : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hx := fun i => (continuous_ofFlat_fst (q := q) i).tendsto c |>.comp hT
  have hy := fun i => (continuous_ofFlat_snd (q := q) i).tendsto c |>.comp hT
  have e1 : ∀ᶠ t in 𝓝[<] sinf W t₀ ŵ, ∀ i j, 1 / ((a : ℝ) + 1) ≤
      (ofFlat (q + 1) (sglue ŵ t)).1 i + (ofFlat (q + 1) (sglue ŵ t)).2 j := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hlt' : 1 / ((a : ℝ) + 1) < C.1 i + C.2 j :=
      ha.trans_le (add_le_add (hmx 0 i (Fin.zero_le _)) (hmy 0 j (Fin.zero_le _)))
    filter_upwards [((hx i).add (hy j)).eventually_const_lt hlt'] with t ht using ht.le
  have e2 : ∀ᶠ t in 𝓝[<] sinf W t₀ ŵ, ∀ i, (ofFlat (q + 1) (sglue ŵ t)).1 i ≤ (b : ℝ) := by
    refine eventually_all.2 fun i => ?_
    filter_upwards [(hx i).eventually_lt_const (hCb i)] with t ht using ht.le
  have e3 : ∀ᶠ t in 𝓝[<] sinf W t₀ ŵ,
      (∃ i k, i < k ∧ (ofFlat (q + 1) (sglue ŵ t)).1 k - (ofFlat (q + 1) (sglue ŵ t)).1 i ≤ δ) ∨
      (∃ i k, i < k ∧ (ofFlat (q + 1) (sglue ŵ t)).2 k - (ofFlat (q + 1) (sglue ŵ t)).2 i ≤ δ) := by
    rcases hp.2 with ⟨i, k, hik, he⟩ | ⟨i, k, hik, he⟩
    · have h0' : C.1 k - C.1 i < δ := by rw [he, sub_self]; exact hδ
      filter_upwards [((hx k).sub (hx i)).eventually_lt_const h0'] with t ht
      exact Or.inl ⟨i, k, hik, ht.le⟩
    · have h0' : C.2 k - C.2 i < δ := by rw [he, sub_self]; exact hδ
      filter_upwards [((hy k).sub (hy i)).eventually_lt_const h0'] with t ht
      exact Or.inr ⟨i, k, hik, ht.le⟩
  have hpos : 0 < sinf W t₀ ŵ := (zero_le).trans_lt (hstrict 0)
  have : (𝓝[<] sinf W t₀ ŵ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  have e0 : ∀ᶠ t in 𝓝[<] sinf W t₀ ŵ, t < sinf W t₀ ŵ := self_mem_nhdsWithin
  obtain ⟨t, ht, h1, h2, h3⟩ := (e0.and (e1.and (e2.and e3))).exists
  obtain ⟨n, hn⟩ := exists_lt_srho ht
  have hmem : (ŵ n).1 t ∈ gapSet (q + 1) (1 / ((a : ℝ) + 1)) b δ := by
    rw [← h.sglue_eq hE.isOpen hn.le]; exact ⟨h1, h2, h3⟩
  refine mem_iUnion.2 ⟨n, ?_⟩
  show pexit (gapSet (q + 1) (1 / ((a : ℝ) + 1)) b δ)ᶜ (ŵ n) < min (pexit (W n) (ŵ n)) t₀
  rw [← coe_srho]
  exact lt_of_le_of_lt (iInf₂_le t fun h' => h' hmem) (WithTop.coe_lt_coe.2 hn)

theorem measurableSet_collSet (hW : ∀ n, IsOpen (W n)) (η K : ℝ) :
    MeasurableSet (collSet W t₀ η K) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun n =>
    measurableSet_hitSet hW (isClosed_gapSet _ _ _ _) n

/-- **`Coll` is null** under the law of the stop sequence of a `B1Family` over an
exhaustion. -/
theorem measure_collLim (hD0 : 0 < D0) {z : Fin ((q + 1) + (q + 1)) → ℝ}
    (hE : IsExh W (flatChamber (q + 1))) (hz : z ∈ W 0) (F : B1Family D0 (q + 1) z)
    {r : ℕ → ℕ} (hr : Monotone r) (hball : ∀ n, W n ⊆ chartQ (q + 1) '' Metric.ball 0 (r n)) :
    (Pq (q + 1)).map (F.stopSeq W t₀ r) (collLim q W t₀) = 0 := by
  have hz' : z ∈ flatChamber (q + 1) := (hE.dom 0).2.2 (subset_closure hz)
  have hΦ := F.measurable_stopSeq (t₀ := t₀) hE.isOpen r
  have hU : MeasurableSet (⋃ a : ℕ, ⋃ b : ℕ, collSet W t₀ (1 / ((a : ℝ) + 1)) (b : ℝ)) :=
    MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => measurableSet_collSet hE.isOpen _ _
  have hnull : (Pq (q + 1)).map (F.stopSeq W t₀ r)
      (⋃ a : ℕ, ⋃ b : ℕ, collSet W t₀ (1 / ((a : ℝ) + 1)) (b : ℝ)) = 0 :=
    measure_iUnion_null fun a => measure_iUnion_null fun b =>
      measure_collSet hD0 hE.dom hE.mono hz F hr hball t₀ (by positivity) _
  rw [Measure.map_apply hΦ (measurableSet_collLim hE.isOpen)]
  rw [Measure.map_apply hΦ hU] at hnull
  refine le_antisymm ((measure_mono_ae ?_).trans hnull.le) bot_le
  filter_upwards [F.ae_isConsAt hD0] with ω hc hω
  obtain ⟨a, b, hab⟩ := collLim_subset (F.isNested_stopSeq hE.isOpen hE.mono hr hball hc) hE
    (by rw [F.stopSeq_zero hz']; exact hz) hω
  exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, hab⟩⟩

end BlockBand.Transmission.Dual.G
