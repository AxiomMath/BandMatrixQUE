module

public import BlockBand.Transmission.LawDuality.KillLevelMart

/-!
# One cap functional for `{x ≤ M, y ≤ 1 − ε}` and its exit time

The cap functional `V_t = Σ_{i<N_t} (x_i + y_i/(1−y_i))` of the dual deletion process and its
first passage time `capTau K` above `K`. Up to `capTau K` the dual coordinates stay in
`{x ≤ K, y ≤ 1 − 1/(1+K)}`, `capTau K` is a stopping time, and `P(capTau K ≤ t) → 0` as `K → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The summand `x + y/(1−y)`. -/
def capFun (w : ℝ × ℝ) : ℝ := w.1 + w.2 / (1 - w.2)

section Defs

variable {Ω : Type*}

/-- `V_t = Σ_{i<N_t} (x_i + y_i/(1−y_i))`. -/
def capV (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (N t ω), capFun (X t ω i, Y t ω i)

/-- First time `V ≥ K`. -/
def capTau (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (K : ℝ) : Ω → WithTop ℝ≥0 :=
  hitLe (fun t ω => -capV N X Y t ω) (-K)

theorem continuousOn_capFun : ContinuousOn capFun kernelDom := by
  refine continuous_fst.continuousOn.add (continuous_snd.continuousOn.div
    (continuous_const.sub continuous_snd).continuousOn fun w hw => ?_)
  exact (sub_pos.2 hw.2).ne'

variable {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}

theorem continuous_capV (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) :
    Continuous fun t => capV N X Y t ω :=
  continuous_pathSum hP continuousOn_capFun (by simp [capFun])

theorem capFun_pos (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (u : ℝ≥0) {i : ℕ} (hi : i < N u ω) :
    0 < X u ω i ∧ 0 < Y u ω i ∧ Y u ω i < 1 ∧ 0 < capFun (X u ω i, Y u ω i) := by
  have hz := hP.chamber u
  have h1 : 0 < X u ω i := hz.2.2.1 ⟨i, hi⟩
  have h2 : 0 < Y u ω i ∧ Y u ω i < 1 := hz.2.2.2 ⟨i, hi⟩
  refine ⟨h1, h2.1, h2.2, ?_⟩
  have : 0 < Y u ω i / (1 - Y u ω i) := div_pos h2.1 (by linarith [h2.2])
  simp only [capFun]; linarith

theorem le_capV (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (u : ℝ≥0) {i : ℕ} (hi : i < N u ω) : capFun (X u ω i, Y u ω i) ≤ capV N X Y u ω :=
  Finset.single_le_sum (f := fun i => capFun (X u ω i, Y u ω i))
    (fun _ hj => (capFun_pos hP u (Finset.mem_range.1 hj)).2.2.2.le) (Finset.mem_range.2 hi)

theorem capV_le_of_le_capTau
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {K : ℝ}
    (h0 : capV N X Y 0 ω < K) {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ capTau N X Y K ω) :
    capV N X Y u ω ≤ K := by
  have hV := continuous_capV hP
  have hlt : ∀ v : ℝ≥0, v < u → capV N X Y v ω < K := fun v hv => by
    by_contra hc
    have : capTau N X Y K ω ≤ v := by
      unfold capTau hitLe
      exact iInf₂_le (f := fun t (_ : -capV N X Y t ω ≤ -K) => (t : WithTop ℝ≥0)) v
        (by linarith [not_lt.1 hc])
    exact absurd (hu.trans this) (not_le.2 (WithTop.coe_lt_coe.2 hv))
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | hpos
  · rw [← h]; exact h0.le
  · have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    refine le_of_tendsto (x := 𝓝[<] u) ((hV.tendsto u).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hlt v hv).le

/-- **Up to `capTau K`: `x_i ≤ K`, `y_j ≤ 1 − 1/(1+K)`.** -/
theorem staysIn_capTau
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {K : ℝ}
    (hK : 0 ≤ K) (h0 : ∀ ω, capV N X Y 0 ω < K) :
    StaysIn N X Y (capTau N X Y K) K (1 / (1 + K)) := by
  intro ω u hu i hi
  have hV := (le_capV (hpath ω) u hi).trans (capV_le_of_le_capTau (hpath ω) (h0 ω) hu)
  obtain ⟨h1, h2, h3, -⟩ := capFun_pos (hpath ω) u hi
  have hq : 0 < Y u ω i / (1 - Y u ω i) := div_pos h2 (by linarith)
  simp only [capFun] at hV
  refine ⟨by linarith, ?_⟩
  have hyK : Y u ω i / (1 - Y u ω i) ≤ K := by linarith
  rw [div_le_iff₀ (by linarith)] at hyK
  rw [show 1 - 1 / (1 + K) = K / (1 + K) by field_simp; ring, le_div_iff₀ (by linarith)]
  nlinarith

theorem total_le_capV (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (u : ℝ≥0) : dualTotal (N u ω) (X u ω) (Y u ω) ≤ capV N X Y u ω := by
  refine Finset.sum_le_sum fun i hi => ?_
  obtain ⟨-, h2, h3, -⟩ := capFun_pos hP u (Finset.mem_range.1 hi)
  have : Y u ω i ≤ Y u ω i / (1 - Y u ω i) :=
    le_div_self h2.le (by linarith) (by linarith)
  simp only [capFun]; linarith

theorem total_le_of_le_capTau
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {K : ℝ}
    (h0 : capV N X Y 0 ω < K) {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ capTau N X Y K ω) :
    dualTotal (N u ω) (X u ω) (Y u ω) ≤ K :=
  (total_le_capV hP u).trans (capV_le_of_le_capTau hP h0 hu)

/-- **Pathwise, `capTau K > t` for every large `K`.** -/
theorem eventually_lt_capTau
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (t : ℝ≥0) :
    ∀ᶠ K in atTop, (t : WithTop ℝ≥0) < capTau N X Y K ω := by
  have hV := continuous_capV hP
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    hV.continuousOn
  filter_upwards [eventually_gt_atTop B] with K hK
  by_contra hc
  have hR : ∀ s, Tendsto (fun u => -capV N X Y u ω) (𝓝[≥] s) (𝓝 (-capV N X Y s ω)) := fun s =>
    ((hV.neg).tendsto s).mono_left nhdsWithin_le_nhds
  obtain ⟨u, hut, hu⟩ := (hitLe_le_iff (V := fun t ω => -capV N X Y t ω) (c := -K) hR t).1
    (not_lt.1 hc)
  have := hB u ⟨zero_le, hut⟩
  rw [Real.norm_eq_abs] at this
  have := le_abs_self (capV N X Y u ω)
  linarith

end Defs

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit m in
theorem measurable_capV_comp {mΩ : MeasurableSpace Ω} {n : Ω → ℕ} {a b : Ω → ℕ → ℝ}
    (hn : Measurable n) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => ∑ i ∈ Finset.range (n ω), capFun (a ω i, b ω i) := by
  have hc : Measurable capFun := by
    unfold capFun; fun_prop
  have hF : Measurable fun z : Ω × ℕ => ∑ i ∈ Finset.range z.2, capFun (a z.1 i, b z.1 i) :=
    measurable_from_prod_countable_left fun k => by
      show Measurable fun x => ∑ i ∈ Finset.range k, capFun (a x i, b x i)
      exact Finset.measurable_fun_sum _ fun i _ =>
        hc.comp ((measurable_pi_iff.1 ha i).prodMk (measurable_pi_iff.1 hb i))
  exact hF.comp (measurable_id.prodMk hn)

theorem isStoppingTime_capTau (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (K : ℝ) :
    IsStoppingTime 𝓖 (capTau N X Y K) :=
  isStoppingTime_hitLe (fun t => (measurable_capV_comp (mΩ := 𝓖 t) (h.adapted t).1
      (h.adapted t).2.1 (h.adapted t).2.2).neg)
    (fun ω t => ((continuous_capV (hpath ω)).neg.tendsto t).mono_left nhdsWithin_le_nhds)
    (fun ω => (continuous_capV (hpath ω)).neg.lowerSemicontinuous) (-K)

/-- **`P(capTau K ≤ t) → 0` as `K → ∞`** (pathwise, no tail estimate). -/
theorem tendsto_measureReal_capTau_le (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (t : ℝ≥0) :
    Tendsto (fun K : ℝ => P.real {ω | capTau N X Y K ω ≤ t}) atTop (𝓝 0) := by
  have := h.prob
  have hmeas : ∀ K : ℝ, MeasurableSet {ω | capTau N X Y K ω ≤ t} := fun K =>
    𝓖.le t _ (isStoppingTime_capTau h hpath K t)
  have e : (fun K : ℝ => P.real {ω | capTau N X Y K ω ≤ t}) =
      fun K => ∫ ω, {ω | capTau N X Y K ω ≤ t}.indicator (1 : Ω → ℝ) ω ∂P :=
    funext fun K => (integral_indicator_one (hmeas K)).symm
  rw [e, show (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂P by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun K => (measurable_one.indicator (hmeas K)).aestronglyMeasurable)
    (Eventually.of_forall fun K => ae_of_all _ fun ω => ?_) (integrable_const 1)
    (ae_of_all _ fun ω => ?_)
  · by_cases hω : ω ∈ {ω | capTau N X Y K ω ≤ t}
    · rw [indicator_of_mem hω]; simp
    · rw [indicator_of_notMem hω]; simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_capTau (hpath ω) t] with K hK
    have : ω ∉ {ω | capTau N X Y K ω ≤ t} := fun h' => absurd h' (not_le.2 hK)
    rw [indicator_of_notMem this]

omit m in
/-- The cap functional at time `0` of a normalized realization is deterministic. -/
theorem capV_zero_eq {ω : Ω} (hstart : N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) :
    capV N X Y 0 ω = ∑ i : Fin p, capFun (x i, y i) := by
  unfold capV
  rw [hstart.1, ← Fin.sum_univ_eq_sum_range (fun i => capFun (X 0 ω i, Y 0 ω i)) p]
  exact Finset.sum_congr rfl fun i _ => by rw [(hstart.2 i).1, (hstart.2 i).2]

end BlockBand.Transmission.LawDuality
