module

public import BlockBand.Transmission.Dual.GCPath
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# `CPath d` is a standard Borel space

`CPath d` is the space of continuous paths `ℝ≥0 → ℝ^d` with the trace of the product σ-algebra.
Its standard Borel structure is obtained by restriction to a fixed dense sequence of times
`qtime`:
* `comap_qres`: the trace σ-algebra is the comap of the restriction `qres` (each evaluation
  `w ↦ w(t)` is a pointwise limit of evaluations at dense times);
* `range_qres`: the range of `qres` is the measurable set `qgood` of dense-time families that
  are uniformly continuous on each bounded set (countably many closed conditions); a family in
  `qgood` extends to a continuous path by limits along `comap qtime (𝓝 t)`;
* hence `qres` is a `MeasurableEmbedding` into the Polish space `ℕ → ℝ^d`, and
  `standardBorelSpace_of_measurableEmbedding` transfers standard Borelness.
So `StandardBorelSpace (CPath d)`, and `ℕ → CPath d` is standard Borel by `pi_countable`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- **Standard Borelness transfers along a measurable embedding.** -/
theorem standardBorelSpace_of_measurableEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] {f : α → β} (hf : MeasurableEmbedding f) :
    StandardBorelSpace α := by
  have hr : StandardBorelSpace (range f) := hf.measurableSet_range.standardBorel
  let e : α ≃ᵐ range f := hf.equivRange
  let τr : TopologicalSpace (range f) := (upgradeStandardBorel (range f)).toTopologicalSpace
  have hPr : PolishSpace (range f) := (upgradeStandardBorel (range f)).toPolishSpace
  let τ : TopologicalSpace α := TopologicalSpace.induced e τr
  have hP : @PolishSpace α τ := e.toEquiv.polishSpace_induced
  have hB : @BorelSpace α τ _ := by
    refine @BorelSpace.mk α τ _ ?_
    rw [borel_comap, ← eq_borel_upgradeStandardBorel (range f)]
    exact e.measurableEmbedding.comap_eq.symm
  exact ⟨⟨τ, hB, hP⟩⟩

variable {d : ℕ}

/-- A fixed dense sequence of times. -/
def qtime : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0

theorem denseRange_qtime : DenseRange qtime := TopologicalSpace.denseRange_denseSeq ℝ≥0

instance neBot_qtime (t : ℝ≥0) : NeBot (comap qtime (𝓝 t)) :=
  comap_neBot_iff.2 fun U hU => by
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := denseRange_qtime.inter_nhds_nonempty hU
    exact ⟨i, hi⟩

theorem exists_qtime_tendsto (t : ℝ≥0) :
    ∃ u : ℕ → ℕ, Tendsto (fun k => qtime (u k)) atTop (𝓝 t) := by
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_qtime t)
  choose u hu using hx
  exact ⟨u, by simpa only [hu] using hlim⟩

/-- Restriction of a continuous path to the dense times. -/
def qres (d : ℕ) (w : CPath d) : ℕ → Fin d → ℝ := fun i => w.1 (qtime i)

theorem measurable_qres : Measurable (qres d) :=
  measurable_pi_iff.2 fun i => measurable_cev (qtime i)

theorem qres_injective : Function.Injective (qres d) := fun w w' h =>
  Subtype.ext (Continuous.ext_on denseRange_qtime w.2 w'.2 (by
    rintro _ ⟨i, rfl⟩; exact congrFun h i))

/-- **The trace σ-algebra of `CPath d` is the comap of the dense-time restriction.** -/
theorem comap_qres :
    MeasurableSpace.comap (qres d) inferInstance = (inferInstance : MeasurableSpace (CPath d)) := by
  refine le_antisymm measurable_qres.comap_le ?_
  have h : Measurable[MeasurableSpace.comap (qres d) inferInstance]
      (Subtype.val : CPath d → ℝ≥0 → Fin d → ℝ) := by
    let _ : MeasurableSpace (CPath d) := MeasurableSpace.comap (qres d) inferInstance
    refine measurable_pi_iff.2 fun t => ?_
    obtain ⟨u, hu⟩ := exists_qtime_tendsto t
    refine @measurable_of_tendsto_metrizable (CPath d) (Fin d → ℝ)
      (MeasurableSpace.comap (qres d) inferInstance) _ _ _ _
      (fun k (w : CPath d) => w.1 (qtime (u k))) _ (fun k => ?_)
      (tendsto_pi_nhds.2 fun w => (w.2.tendsto t).comp hu)
    exact (measurable_pi_apply (u k)).comp (comap_measurable (qres d))
  exact h.comap_le

/-- Dense-time families that are uniformly continuous on every bounded set. -/
def qgood (d : ℕ) : Set (ℕ → Fin d → ℝ) :=
  ⋂ n : ℕ, ⋂ k : ℕ, ⋃ m : ℕ, ⋂ i : ℕ, ⋂ j : ℕ,
    {v | ¬(qtime i ≤ n ∧ qtime j ≤ n ∧ dist (qtime i) (qtime j) < 1 / ((m : ℝ) + 1)) ∨
      dist (v i) (v j) ≤ 1 / ((k : ℝ) + 1)}

theorem measurableSet_qgood : MeasurableSet (qgood d) := by
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => MeasurableSet.iUnion
    fun m => MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  rw [ofPred_or]
  exact (MeasurableSet.const _).union
    (measurableSet_le ((measurable_pi_apply i).dist (measurable_pi_apply j)) measurable_const)

theorem qgood_unif {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) (n k : ℕ) : ∃ m : ℕ, ∀ i j,
    qtime i ≤ n → qtime j ≤ n → dist (qtime i) (qtime j) < 1 / ((m : ℝ) + 1) →
      dist (v i) (v j) ≤ 1 / ((k : ℝ) + 1) := by
  simp only [qgood, mem_iInter, mem_iUnion, mem_ofPred_eq] at hv
  obtain ⟨m, hm⟩ := hv n k
  exact ⟨m, fun i j hi hj hd => (hm i j).resolve_left fun h => h ⟨hi, hj, hd⟩⟩

theorem qres_mem_qgood (w : CPath d) : qres d w ∈ qgood d := by
  simp only [qgood, mem_iInter, mem_iUnion, mem_ofPred_eq]
  intro n k
  have hu := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (n : ℝ≥0))).uniformContinuousOn_of_continuous
    w.2.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff_le.1 hu (1 / ((k : ℝ) + 1))
    (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun i j => ?_⟩
  by_cases h : qtime i ≤ n ∧ qtime j ≤ n ∧ dist (qtime i) (qtime j) < 1 / ((m : ℝ) + 1)
  · exact Or.inr (hδu _ ⟨zero_le, h.1⟩ _ ⟨zero_le, h.2.1⟩ (h.2.2.trans hm).le)
  · exact Or.inl h

/-- The local form of `qgood`: near `t`, the family oscillates by at most `1/(k+1)`. -/
theorem qgood_local {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) (t : ℝ≥0) (k : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, dist (qtime i) t < r → dist (qtime j) t < r →
      dist (v i) (v j) ≤ 1 / ((k : ℝ) + 1) := by
  obtain ⟨m, hm⟩ := qgood_unif hv (⌈(t : ℝ)⌉₊ + 1) k
  refine ⟨min 1 (1 / (2 * ((m : ℝ) + 1))), by positivity, fun i j hi hj => hm i j ?_ ?_ ?_⟩
  · have h1 := (hi.trans_le (min_le_left _ _))
    rw [NNReal.dist_eq] at h1
    have h2 := Nat.le_ceil (t : ℝ)
    have h3 := (abs_lt.1 h1).2
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  · have h1 := (hj.trans_le (min_le_left _ _))
    rw [NNReal.dist_eq] at h1
    have h2 := Nat.le_ceil (t : ℝ)
    have h3 := (abs_lt.1 h1).2
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  · have h1 := hi.trans_le (min_le_right _ _)
    have h2 := hj.trans_le (min_le_right _ _)
    calc dist (qtime i) (qtime j) ≤ dist (qtime i) t + dist (qtime j) t :=
          dist_triangle_right _ _ _
      _ < 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * ((m : ℝ) + 1)) := add_lt_add h1 h2
      _ = 1 / ((m : ℝ) + 1) := by field_simp; ring

theorem eventually_qtime_near (t : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in comap qtime (𝓝 t), dist (qtime i) t < r :=
  preimage_mem_comap (Metric.ball_mem_nhds t hr)

theorem exists_tendsto_qgood {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) (t : ℝ≥0) :
    ∃ c, Tendsto v (comap qtime (𝓝 t)) (𝓝 c) := by
  have hc : Cauchy (map v (comap qtime (𝓝 t))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨r, hr, hloc⟩ := qgood_local hv t k
    refine ⟨v '' {i | dist (qtime i) t < r}, image_mem_map (eventually_qtime_near t hr), ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact (hloc i j hi hj).trans_lt hk
  obtain ⟨c, hc⟩ := CompleteSpace.complete hc
  exact ⟨c, hc⟩

/-- The continuous extension of a `qgood` family. -/
def qlim (v : ℕ → Fin d → ℝ) (t : ℝ≥0) : Fin d → ℝ := limUnder (comap qtime (𝓝 t)) v

theorem dist_qlim_le {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) (t : ℝ≥0) {c : Fin d → ℝ} {ε : ℝ}
    (h : ∀ᶠ j in comap qtime (𝓝 t), dist (v j) c ≤ ε) : dist (qlim v t) c ≤ ε :=
  le_of_tendsto (((tendsto_nhds_limUnder (exists_tendsto_qgood hv t))).dist tendsto_const_nhds) h

theorem qlim_qtime {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) (i : ℕ) : qlim v (qtime i) = v i := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨r, hr, hloc⟩ := qgood_local hv (qtime i) k
  refine dist_qlim_le hv _ ((eventually_qtime_near (qtime i) hr).mono fun j hj => ?_)
  exact (hloc j i hj (by rw [dist_self]; exact hr)).trans hk.le

theorem continuous_qlim {v : ℕ → Fin d → ℝ} (hv : v ∈ qgood d) : Continuous (qlim v) := by
  refine Metric.continuous_iff.2 fun t ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨r, hr, hloc⟩ := qgood_local hv t k
  refine ⟨r / 2, half_pos hr, fun t' ht' => ?_⟩
  have hb : dist (qlim v t') (qlim v t) ≤ 1 / ((k : ℝ) + 1) := by
    refine dist_qlim_le hv t' ((eventually_qtime_near t' (half_pos hr)).mono fun j hj => ?_)
    rw [dist_comm]
    refine dist_qlim_le hv t ((eventually_qtime_near t hr).mono fun i hi => hloc i j hi ?_)
    calc dist (qtime j) t ≤ dist (qtime j) t' + dist t' t := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hj ht'
      _ = r := add_halves r
  linarith

/-- **The range of the restriction is `qgood`.** -/
theorem range_qres : range (qres d) = qgood d := by
  refine Subset.antisymm (range_subset_iff.2 qres_mem_qgood) fun v hv => ?_
  exact ⟨⟨qlim v, continuous_qlim hv⟩, funext fun i => qlim_qtime hv i⟩

/-- **The dense-time restriction is a measurable embedding.** -/
theorem measurableEmbedding_qres : MeasurableEmbedding (qres d) where
  injective := qres_injective
  measurable := measurable_qres
  measurableSet_image' := by
    intro s hs
    have hs' : MeasurableSet[MeasurableSpace.comap (qres d) inferInstance] s := by
      rw [comap_qres]; exact hs
    obtain ⟨t, ht, rfl⟩ := hs'
    rw [image_preimage_eq_inter_range, range_qres]
    exact ht.inter measurableSet_qgood

/-- **`CPath d` is a standard Borel space.** -/
instance standardBorelSpace_cpath : StandardBorelSpace (CPath d) :=
  standardBorelSpace_of_measurableEmbedding measurableEmbedding_qres

example : StandardBorelSpace (ℕ → CPath d) := inferInstance

end BlockBand.Transmission.Dual.G
