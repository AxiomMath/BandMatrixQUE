module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Telescope
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Measurability of exit events and stopped paths on a raw filtration

`(Ω, m₀, Q)`, raw filtration `𝓖`, `Y` adapted with a.s. continuous paths in `ℝ^d`, `W` open.
The exit time `τ = exitTimeFrom W Y` need not be a stopping time. Still:

* `exists_set_lt_exit`: for each `u` there is `E_u ∈ 𝓖_u` with `E_u = {u < τ}` on every
  continuous path (built from dyadic times and the closed sets `{dist(·, Wᶜ) ≥ 1/(m+1)}`);
* `aesm_stoppedProcess_exit`: `Y_{t∧τ}` is `𝓖_t`-a.e.-strongly measurable (telescoping
  approximation along the grids of `[0, t]`).
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

/-- Dyadic lower approximations of a time. -/
def dyad (j : ℕ) (v : ℝ≥0) : ℝ≥0 := (⌊v * 2 ^ j⌋₊ : ℝ≥0) / 2 ^ j

theorem dyad_le (j : ℕ) (v : ℝ≥0) : dyad j v ≤ v := by
  unfold dyad
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem tendsto_dyad (v : ℝ≥0) : Tendsto (fun j => dyad j v) atTop (𝓝 v) := by
  rw [← NNReal.tendsto_coe]
  have hlim : Tendsto (fun j : ℕ => (v : ℝ) - (1 / 2 : ℝ) ^ j) atTop (𝓝 v) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_)
    (fun j => by exact_mod_cast dyad_le j v)
  have h := Nat.lt_floor_add_one ((v : ℝ) * 2 ^ j)
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  simp only [dyad, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
  rw [le_div_iff₀ hp, one_div, inv_pow, sub_mul, inv_mul_cancel₀ hp.ne']
  have : (⌊v * 2 ^ j⌋₊ : ℝ) = ⌊(v : ℝ) * 2 ^ j⌋₊ := by
    congr 1
  rw [this]
  linarith

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ} {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m₀} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}

/-- The closed sets `{y | 1/(m+1) ≤ dist(y, Wᶜ)}`. -/
def innerSet (W : Set (Fin d → ℝ)) (m : ℕ) : Set (Fin d → ℝ) :=
  {y | 1 / ((m : ℝ) + 1) ≤ infDist y Wᶜ}

theorem isClosed_innerSet (m : ℕ) : IsClosed (innerSet W m) :=
  isClosed_le continuous_const (continuous_infDist_pt _)

theorem innerSet_subset (m : ℕ) : innerSet W m ⊆ W := by
  intro y hy
  by_contra hyW
  have : infDist y Wᶜ = 0 := infDist_zero_of_mem hyW
  have hpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hy' : 1 / ((m : ℝ) + 1) ≤ infDist y Wᶜ := hy
  linarith

/-- **Exit events are a.s. in the raw filtration.** -/
theorem exists_set_lt_exit (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hW : IsOpen W)
    (u : ℝ≥0) : ∃ E : Set Ω, MeasurableSet[𝓖 u] E ∧ ∀ ω, Continuous (fun t => Y t ω) →
      (ω ∈ E ↔ (u : WithTop ℝ≥0) < exitTimeFrom W Y ω) := by
  rcases (Wᶜ).eq_empty_or_nonempty with hne | hne
  · refine ⟨univ, MeasurableSet.univ, fun ω _ => ?_⟩
    have : exitTimeFrom W Y ω = ⊤ := iInf₂_eq_top.2 fun t ht =>
      absurd (show Y t ω ∈ Wᶜ from ht) (by rw [hne]; exact id)
    simp only [this, mem_univ, true_iff]
    exact WithTop.coe_lt_top u
  classical
  set E : Set Ω := ⋃ m : ℕ, ({ω | Y u ω ∈ innerSet W m} ∩
    ⋂ j : ℕ, ⋂ k : ℕ, {ω | (k : ℝ≥0) / 2 ^ j ≤ u → Y ((k : ℝ≥0) / 2 ^ j) ω ∈ innerSet W m})
  refine ⟨E, ?_, fun ω hω => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine MeasurableSet.iUnion fun m => (((hY u).measurable (isClosed_innerSet (W := W) m).measurableSet)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_)
    by_cases hq : (k : ℝ≥0) / 2 ^ j ≤ u
    · have := 𝓖.mono hq _ ((hY ((k : ℝ≥0) / 2 ^ j)).measurable
        (isClosed_innerSet (W := W) m).measurableSet)
      convert this using 1
      ext ω; simp [hq]
    · convert MeasurableSet.univ using 1
      ext ω; simp [hq]
  · obtain ⟨m, hmu, hmq⟩ := mem_iUnion.1 h
    have hall : ∀ v ≤ u, Y v ω ∈ innerSet W m := by
      intro v hv
      refine (isClosed_innerSet m).mem_of_tendsto ((hω.tendsto v).comp (tendsto_dyad v))
        (Eventually.of_forall fun j => ?_)
      have := mem_iInter.1 (mem_iInter.1 hmq j) ⌊v * 2 ^ j⌋₊
      exact this ((dyad_le j v).trans hv)
    by_contra hlt
    push Not at hlt
    rcases exitTimeFrom_attained hW hω with h1 | ⟨s₀, h1, h2⟩
    · rw [h1] at hlt; exact absurd hlt (not_le.2 (WithTop.coe_lt_top u))
    · rw [h1] at hlt
      exact h2 (innerSet_subset m (hall s₀ (WithTop.coe_le_coe.1 hlt)))
  · have hin : ∀ v ∈ Icc (0 : ℝ≥0) u, Y v ω ∈ W := fun v hv =>
      mem_of_lt_exitTimeFrom (lt_of_le_of_lt (WithTop.coe_le_coe.2 hv.2) h)
    have hcont : ContinuousOn (fun v => infDist (Y v ω) Wᶜ) (Icc 0 u) :=
      ((continuous_infDist_pt _).comp hω).continuousOn
    obtain ⟨v₀, hv₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.2 zero_le⟩ hcont
    have hpos : 0 < infDist (Y v₀ ω) Wᶜ :=
      (hW.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h' => h' (hin v₀ hv₀))
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    have hall : ∀ v ∈ Icc (0 : ℝ≥0) u, Y v ω ∈ innerSet W m := fun v hv =>
      le_trans hm.le (hmin hv)
    refine mem_iUnion.2 ⟨m, hall u ⟨zero_le, le_rfl⟩, mem_iInter.2 fun j => mem_iInter.2
      fun k hk => hall _ ⟨zero_le, hk⟩⟩

/-- **The stopped path at the exit time is a.e. adapted.** -/
theorem aesm_stoppedProcess_exit (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) (hW : IsOpen W) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (stoppedProcess Y (exitTimeFrom W Y) t) Q := by
  choose E hEm hE using exists_set_lt_exit (𝓖 := 𝓖) hY hW
  have h0t : (0 : ℝ≥0) ≤ t := zero_le
  set S : ℕ → Ω → Fin d → ℝ := fun n ω => Y 0 ω + ∑ k ∈ Finset.range (n + 1),
    (E (grid 0 t n k)).indicator (fun ω => Y (grid 0 t n (k + 1)) ω - Y (grid 0 t n k) ω) ω
  have hSm : ∀ n, StronglyMeasurable[𝓖 t] (S n) := by
    intro n
    refine ((hY 0).mono (𝓖.mono h0t)).add (Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_)
    have hk := Finset.mem_range.1 hk
    have l0 := 𝓖.mono (show grid 0 t n k ≤ t by
      have := grid_mono h0t n hk.le; rwa [grid_last h0t] at this)
    have l1 := 𝓖.mono (show grid 0 t n (k + 1) ≤ t by
      have := grid_mono h0t n (Nat.succ_le_of_lt hk); rwa [grid_last h0t] at this)
    exact (((hY _).mono l1).sub ((hY _).mono l0)).indicator (l0 _ (hEm _))
  refine aestronglyMeasurable_of_tendsto_ae_sub (fun n => (hSm n).aestronglyMeasurable) ?_
  filter_upwards [hc] with ω hω
  have := (tendsto_telescope hω (exitTimeFrom W Y ω) t).const_add (Y 0 ω)
  rw [add_sub_cancel] at this
  refine this.congr fun n => ?_
  simp only [S]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (grid 0 t n k : WithTop ℝ≥0) < exitTimeFrom W Y ω
  · simp only [h, ↓reduceIte, Set.indicator_of_mem ((hE _ ω hω).2 h)]
  · simp only [h, ↓reduceIte, Set.indicator_of_notMem (fun h' => h ((hE _ ω hω).1 h'))]

end BlockBand.SourceProcess.Stochastic.Semimartingale
