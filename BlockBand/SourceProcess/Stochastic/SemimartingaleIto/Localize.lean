module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Exhaustion of an open set and exit times)

For open `U ⊆ ℝ^d`: `exhaust U m = {‖y‖ < m, infEDist(y, Uᶜ) > 1/(m+1)}` is open, increasing in
`m`, has compact closure inside `U`, and every compact subset of `U` lies in some
`exhaust U m` (`exists_exhaust_of_compact`). On a continuous path in `U` the exit times from
`exhaust U m` tend to `⊤` (`tendsto_exitTimeFrom_exhaust`). Raw stopping times equal to these
exit times on continuous paths: `rawHit (exhaust U m)ᶜ Y` (`isStoppingTime_rawHit`,
`rawHit_compl_eq_exitTimeFrom`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The exhaustion of `U`. -/
def exhaust (U : Set (Fin d → ℝ)) (m : ℕ) : Set (Fin d → ℝ) :=
  {y | ‖y‖ < m ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1)) < infEDist y Uᶜ}

variable {U : Set (Fin d → ℝ)}

theorem isOpen_exhaust (m : ℕ) : IsOpen (exhaust U m) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_infEDist)

theorem closure_exhaust_subset (m : ℕ) : closure (exhaust U m) ⊆
    {y | ‖y‖ ≤ m ∧ ENNReal.ofReal (1 / ((m : ℝ) + 1)) ≤ infEDist y Uᶜ} := by
  refine closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const continuous_infEDist)

theorem closure_exhaust_subset_U (m : ℕ) : closure (exhaust U m) ⊆ U := by
  intro y hy
  have h := (closure_exhaust_subset m hy).2
  by_contra hyU
  rw [infEDist_zero_of_mem (show y ∈ Uᶜ from hyU)] at h
  have : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((m : ℝ) + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  exact absurd h (not_le.2 this)

theorem isCompact_closure_exhaust (m : ℕ) : IsCompact (closure (exhaust U m)) := by
  refine isCompact_of_isClosed_isBounded isClosed_closure ?_
  refine (isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := m)).subset fun y hy => ?_
  rw [mem_closedBall, dist_zero_right]
  exact (closure_exhaust_subset m hy).1

theorem exhaust_mono : Monotone (exhaust U) := by
  intro m n hmn y hy
  have h1 : (m : ℝ) ≤ n := by exact_mod_cast hmn
  refine ⟨hy.1.trans_le h1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hy.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem iUnion_exhaust (hU : IsOpen U) : (⋃ m, exhaust U m) = U := by
  refine Subset.antisymm (iUnion_subset fun m => subset_closure.trans
    (closure_exhaust_subset_U m)) fun y hy => ?_
  have hpos : 0 < infEDist y Uᶜ := by
    rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq]; exact fun h => h hy
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  obtain ⟨m₁, hm₁⟩ := exists_nat_one_div_lt (ENNReal.ofReal_pos.1 hr1)
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt ‖y‖
  refine mem_iUnion.2 ⟨max m₁ m₂, ?_, ?_⟩
  · exact hm₂.trans_le (by exact_mod_cast le_max_right _ _)
  · refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) (lt_of_le_of_lt
      (ENNReal.ofReal_le_ofReal hm₁.le) hr2)
    have h1 : (m₁ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_left m₁ m₂
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem exists_exhaust_of_compact (hU : IsOpen U) {C : Set (Fin d → ℝ)} (hC : IsCompact C)
    (hCU : C ⊆ U) : ∃ m, C ⊆ exhaust U m :=
  hC.elim_directed_cover (exhaust U) isOpen_exhaust (by rw [iUnion_exhaust hU]; exact hCU)
    exhaust_mono.directed_le

/-- On a continuous path in `U`, the exit times from the exhaustion tend to `⊤`. -/
theorem tendsto_exitTimeFrom_exhaust {Ω : Type*} (hU : IsOpen U) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {ω : Ω} (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) :
    Tendsto (fun m => exitTimeFrom (exhaust U m) Y ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  have hC : IsCompact ((fun t => Y t ω) '' Icc 0 (T + 1)) := isCompact_Icc.image hY
  obtain ⟨m₀, hm₀⟩ := exists_exhaust_of_compact hU hC (by
    rintro _ ⟨t, -, rfl⟩; exact hYU t)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one T)) (le_iInf₂ fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  exact hs (exhaust_mono hm (hm₀ ⟨s, ⟨zero_le, (WithTop.coe_lt_coe.1 hlt).le⟩, rfl⟩))

theorem rawHit_compl_eq_exitTimeFrom {Ω : Type*} {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hY : Continuous fun t => Y t ω) :
    rawHit Wᶜ Y ω = exitTimeFrom W Y ω :=
  rawHit_eq_hitTime hW.isClosed_compl hY

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
