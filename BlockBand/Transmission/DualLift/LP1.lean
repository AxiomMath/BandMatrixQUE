module

public import BlockBand.Transmission.DualLift.LUpcross

/-!
# The corner limit along the lift: `S → 0` at a finite lifetime

Boundary and random starts; `ζ = sup_n e_n`. `ae_good_conv`: almost surely `ω ∈ good`
(invariance of `liftM`, radius consistency) and, if `ζ < ∞`, then for every `k` there is
`s₀ < ζ` with `S < 1/(k+1)` along every path `n` on `[s₀, e_n]` (`IsConv`). The start may be
random and unbounded: the estimates are applied on the `𝓖₀`-events `A_B = {g(π ξ) ≤ B}`,
`B ∈ ℕ`, which exhaust the space.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- The lifetime `ζ = sup_n e_n`. -/
def zeta (ω : LΩ S) : WithTop ℝ≥0 := ⨆ n, F.e n ω

/-- Pathwise convergence of `S` to `0` at a finite `ζ`. -/
def IsConv (ω : LΩ S) : Prop := F.zeta ω < ⊤ → ∀ k : ℕ, ∃ s₀ : ℝ≥0,
  (s₀ : WithTop ℝ≥0) < F.zeta ω ∧
  ∀ (n : ℕ) (s : ℝ≥0), s₀ ≤ s → (s : WithTop ℝ≥0) ≤ F.e n ω → F.Sp n s ω < 1 / ((k : ℝ) + 1)

theorem e_le_zeta (n : ℕ) (ω : LΩ S) : F.e n ω ≤ F.zeta ω := le_iSup (fun n => F.e n ω) n

theorem Sp_eq_of_good {ω : LΩ S} (h : ω ∈ F.good) {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Sp n t ω = F.Sp m t ω := by
  simp only [Sp, F.Yf_of_good h, Zp, ((F.good_spec h).2 n m hnm).2 t ht]

/-- On a good path with finite `ζ`, every `e_n` is strictly before `ζ`. -/
theorem e_lt_zeta {ω : LΩ S} (h : ω ∈ F.good) (hζ : F.zeta ω < ⊤) (n : ℕ) :
    F.e n ω < F.zeta ω := by
  have hc := (F.good_spec h).2
  refine lt_of_le_of_ne (F.e_le_zeta n ω) fun heq => ?_
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hζ.ne
  obtain ⟨k, hk⟩ := exists_nat_ge (max (n : ℝ) ‖ξ ω‖)
  have hnk : n ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
  have hek : ∀ j, n ≤ j → F.e j ω = m := fun j hj => le_antisymm (hm ▸ F.e_le_zeta j ω)
    (hm ▸ heq ▸ (hc n j hj).1)
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ ‖F.X (k + 1) m ω‖ :=
    le_norm_exitTimeOf (F.continuous_X (k + 1) ω) (hek (k + 1) (by omega))
  have h2 : F.X k m ω = F.X (k + 1) m ω := (hc k (k + 1) (by omega)).2 m (by rw [hek k hnk])
  have h3 := F.norm_X_le k m ω
  have h4 : max (k : ℝ) ‖ξ ω‖ = k := max_eq_left ((le_max_right _ _).trans hk)
  rw [h2, h4] at h3
  push_cast at h1
  linarith

theorem hitS_eq_of_good {ω : LΩ S} (h : ω ∈ F.good) {n m : ℕ} (hnm : n ≤ m) {ε : ℝ}
    (hle : F.hitS n ε ω ≤ F.e n ω) : F.hitS m ε ω = F.hitS n ε ω := by
  have hR : ∀ j t, Tendsto (fun u => F.Sp j u ω) (𝓝[≥] t) (𝓝 (F.Sp j t ω)) := fun j t =>
    SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp j ω) t
  apply le_antisymm
  · cases hτ : F.hitS n ε ω with
    | top => exact le_top
    | coe r =>
      have hr : F.Sp n r ω ≤ ε := hitLe_attained (hR n) hτ
      rw [F.Sp_eq_of_good h hnm (hτ ▸ hle)] at hr
      exact iInf₂_le r hr
  · refine le_iInf₂ fun t ht => ?_
    by_cases htn : (t : WithTop ℝ≥0) ≤ F.e n ω
    · rw [← F.Sp_eq_of_good h hnm htn] at ht
      exact iInf₂_le t ht
    · exact hle.trans (not_le.1 htn).le

/-- `S` comes back to `a` arbitrarily close to a finite `ζ < T`. -/
def Bad (a : ℝ) (T : ℕ) : Set (LΩ S) :=
  {ω | ω ∈ F.good ∧ F.zeta ω < (T : ℝ≥0) ∧ ∀ s₀ : ℝ≥0, (s₀ : WithTop ℝ≥0) < F.zeta ω →
    ∃ (n : ℕ) (s : ℝ≥0), s₀ ≤ s ∧ (s : WithTop ℝ≥0) ≤ F.e n ω ∧ a ≤ F.Sp n s ω}

/-- The paths that never reach `{S ≤ ε}` before their exit. -/
def NoHit (ε : ℝ) (T : ℕ) : Set (LΩ S) :=
  {ω | ω ∈ F.good ∧ ∀ n : ℕ, F.e n ω < F.hitS n ε ω ∧ F.e n ω < ((T : ℝ≥0) : WithTop ℝ≥0)}

/-- The `n`-th return event of estimate B. -/
def Up (n : ℕ) (ε a : ℝ) (T : ℕ) : Set (LΩ S) :=
  {ω | F.hitS n ε ω < ((T : ℝ≥0) : WithTop ℝ≥0) ∧ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧
    F.hitS n ε ω ≤ s ∧ a ≤ F.Sp n s ω}

theorem bad_subset {a ε : ℝ} (T : ℕ) :
    F.Bad a T ⊆ F.NoHit ε T ∪ ⋃ N : ℕ, ⋂ n ∈ Ici N, F.Up n ε a T := by
  rintro ω ⟨hc, hζ, hB⟩
  by_cases hω : ω ∈ F.NoHit ε T
  · exact Or.inl hω
  right
  have hζ' : F.zeta ω < ⊤ := lt_of_lt_of_le hζ le_top
  have hω' : ¬∀ n : ℕ, F.e n ω < F.hitS n ε ω ∧ F.e n ω < ((T : ℝ≥0) : WithTop ℝ≥0) :=
    fun hall => hω ⟨hc, hall⟩
  obtain ⟨n₀, hn₀⟩ := not_forall.1 hω'
  have hen₀ : F.e n₀ ω < (T : ℝ≥0) := (F.e_le_zeta n₀ ω).trans_lt hζ
  have hhit : F.hitS n₀ ε ω ≤ F.e n₀ ω := by
    by_contra hc'; exact hn₀ ⟨not_le.1 hc', hen₀⟩
  have hlt : F.hitS n₀ ε ω < F.zeta ω := hhit.trans_lt (F.e_lt_zeta hc hζ' n₀)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  obtain ⟨n₁, s, hrs, hsn, has⟩ := hB r (hr ▸ hlt)
  refine mem_iUnion.2 ⟨max n₀ n₁, mem_iInter₂.2 fun n hn => ?_⟩
  have hn₀n : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁n : n₁ ≤ n := (le_max_right _ _).trans hn
  have hτ : F.hitS n ε ω = r := by rw [F.hitS_eq_of_good hc hn₀n hhit, hr]
  have hsT : (s : WithTop ℝ≥0) < (T : ℝ≥0) := hsn.trans_lt ((F.e_le_zeta n₁ ω).trans_lt hζ)
  refine ⟨?_, s, (WithTop.coe_lt_coe.1 hsT).le, by rw [hτ]; exact WithTop.coe_le_coe.2 hrs, ?_⟩
  · rw [hτ]; exact (WithTop.coe_le_coe.2 hrs).trans_lt hsT
  · rwa [← F.Sp_eq_of_good hc hn₁n hsn]

/-- The `𝓖₀`-event `{g(π ξ) ≤ B}`. -/
def startBd (B : ℝ) : Set (LΩ S) := {ω | liftLyap (liftProj (ξ ω)) ≤ B}

omit [IsProbabilityMeasure μ] in
theorem measurableSet_startBd (hξ : IsLiftStart μ ξ) (B : ℝ) :
    MeasurableSet[L𝓖 μ 0] (startBd (ξ := ξ) B) :=
  (measurable_liftLyap.comp (contDiff_liftProj.continuous.measurable.comp
    hξ.meas.measurable)) measurableSet_Iic

omit [IsProbabilityMeasure μ] in
theorem tot_le_of_startBd (hξ : IsLiftStart μ ξ) {B : ℝ} {ω : LΩ S}
    (h : ω ∈ startBd (ξ := ξ) B) : tot (liftProj (ξ ω)) ≤ B := by
  have hm := hξ.mem ω
  have hy := ly_mem_of_mem hm
  exact (le_liftLyap ⟨lx_nonneg _, hy.1, hy.2, lS_pos hm⟩).trans h

theorem measure_noHit (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) {ε : ℝ} (hε0 : 0 < ε) (T : ℕ)
    (B : ℝ) : LP μ (startBd (ξ := ξ) B ∩ F.NoHit ε T) = 0 := by
  have ha : 0 < exp (-(D0 / 2) * (T : ℝ≥0)) * ε := mul_pos (exp_pos _) hε0
  refine eq_zero_of_forall_mul_le (measure_ne_top _ _) ha (D := B) fun M hM => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (max (exp (1 + M)) (1 / ε + 2))
  have hn2 : (2 : ℝ) ≤ n := by
    have : (0 : ℝ) ≤ 1 / ε := by positivity
    linarith [le_max_right (exp (1 + M)) (1 / ε + 2)]
  have hlog : 1 + M ≤ Real.log (1 + n * n) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [le_max_left (exp (1 + M)) (1 / ε + 2)]
  have hmr := le_max_right (exp (1 + M)) (1 / ε + 2)
  have h := F.measure_noHit_le hD0 hξ n hε0 (by linarith) (by linarith) (T : ℝ≥0)
    (measurableSet_startBd hξ B)
    (B := B) fun ω hω => hω
  refine le_trans ?_ h
  rw [mul_comm]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
    (measure_mono fun ω hω => ⟨⟨hω.1, hω.2.1⟩, hω.2.2 n⟩)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hε0.le) (exp_pos _).le

theorem measure_liminf_up (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) {ε a : ℝ} (hε : 0 < ε)
    (ha : 0 < a) (T : ℕ) (B : ℝ) :
    LP μ (startBd (ξ := ξ) B ∩ ⋃ N : ℕ, ⋂ n ∈ Ici N, F.Up n ε a T) ≤ ENNReal.ofReal (ε / a) := by
  have hmono : Monotone fun N : ℕ => startBd (ξ := ξ) B ∩ ⋂ n ∈ Ici N, F.Up n ε a T :=
    fun N M hNM => inter_subset_inter_right _ (biInter_mono (Ici_subset_Ici.2 hNM) fun _ _ => le_rfl)
  rw [inter_iUnion, hmono.measure_iUnion]
  refine iSup_le fun N => (measure_mono (inter_subset_inter_right _
    (biInter_subset_of_mem (mem_Ici.2 le_rfl)))).trans ?_
  exact F.measure_upcross_le hD0 hξ N hε ha (T : ℝ≥0) (measurableSet_startBd hξ B)
    (B := B) fun ω hω => tot_le_of_startBd hξ hω

theorem measure_bad (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (k T : ℕ) (B : ℝ) :
    LP μ (startBd (ξ := ξ) B ∩ F.Bad (1 / ((k : ℝ) + 1)) T) = 0 := by
  set a : ℝ := 1 / ((k : ℝ) + 1) with hadef
  have ha : 0 < a := by positivity
  have hb : ∀ j : ℕ, LP μ (startBd (ξ := ξ) B ∩ F.Bad a T) ≤
      ENNReal.ofReal (1 / ((j : ℝ) + 1)) := fun j => by
    set ε : ℝ := a / ((j : ℝ) + 2) with hεdef
    have hε : 0 < ε := by positivity
    refine (measure_mono (inter_subset_inter_right _ (F.bad_subset (ε := ε) T))).trans ?_
    rw [inter_union_distrib_left]
    refine (measure_union_le _ _).trans ?_
    rw [F.measure_noHit hD0 hξ hε T B, zero_add]
    refine (F.measure_liminf_up hD0 hξ hε ha T B).trans (ENNReal.ofReal_le_ofReal ?_)
    have he : ε / a = 1 / ((j : ℝ) + 2) := by rw [hεdef]; field_simp
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_antisymm (ge_of_tendsto' ht hb) bot_le

/-- **The corner limit (pathwise form)**: almost surely the path is good and `S → 0` at a
finite `ζ`. -/
theorem ae_good_conv (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) :
    ∀ᵐ ω ∂LP μ, ω ∈ F.good ∧ F.IsConv ω := by
  have hnull : ∀ᵐ ω ∂LP μ, ∀ k T B : ℕ, ω ∉ startBd (ξ := ξ) B ∩ F.Bad (1 / ((k : ℝ) + 1)) T := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro T
    rw [ae_all_iff]; intro B
    exact measure_eq_zero_iff_ae_notMem.1 (F.measure_bad hD0 hξ k T B)
  have hG : ∀ᵐ ω ∂LP μ, ω ∈ F.good := by rw [ae_iff]; exact F.measure_good_compl hD0 hξ
  filter_upwards [hG, hnull] with ω hc hb
  refine ⟨hc, fun hζ k => ?_⟩
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hζ.ne
  obtain ⟨T, hT⟩ := exists_nat_gt (m : ℝ)
  obtain ⟨B, hB⟩ := exists_nat_ge (liftLyap (liftProj (ξ ω)))
  have hζT : F.zeta ω < ((T : ℝ≥0) : WithTop ℝ≥0) := by
    rw [← hm]; exact WithTop.coe_lt_coe.2 (by exact_mod_cast hT)
  have h := hb k T B
  simp only [Bad, startBd, mem_inter_iff, mem_ofPred_eq, not_and, not_forall, not_exists,
    not_le] at h
  obtain ⟨s₀, hs₀, hS⟩ := h hB hc hζT
  exact ⟨s₀, hs₀, fun n s h1 h2 => hS n s h1 h2⟩

end LiftFamily

end BlockBand.Transmission.DualLift
