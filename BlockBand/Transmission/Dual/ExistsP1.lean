module

public import BlockBand.Transmission.Dual.ExistsBoundary
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionExit

/-!
# `exists_` at `p = 1`: the corner limit at the lifetime

`ae_tendsto`: almost surely, the family is consistent (`IsCons`) and, if `ζ < ∞`, then for
every `k` there is `s₀ < ζ` such that `S < 1/(k+1)` along every path `n` on `[s₀, e_n]`
(`IsConv`). So `S = x + y → 0` as `t ↑ ζ`: both coordinates tend to the corner.

Proof: for `a = 1/(k+1)`, `T ∈ ℕ`, the set `Bad` of consistent paths with `ζ < T` that come
back to `{S ≥ a}` arbitrarily close to `ζ` is covered, for every `0 < ε < a`, by
`{∀ n, e_n < hitS n ε, e_n < T}` (null by estimate A, letting `n → ∞`) and by
`liminf_n {hitS n ε < T, S reaches a after hitS n ε before T}` (measure `≤ ε/a` by estimate B
and continuity from below). Consistency makes `hitS n ε` eventually constant in `n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z)

/-- The exhaustion time `ζ = sup_n e_n`. -/
def zeta (ω : Ω₁) : WithTop ℝ≥0 := ⨆ n, F.e n ω

/-- Pathwise consistency of the family. -/
def IsCons (ω : Ω₁) : Prop := ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
  ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω

/-- Pathwise convergence of `S` to `0` at a finite `ζ`. -/
def IsConv (ω : Ω₁) : Prop := F.zeta ω < ⊤ → ∀ k : ℕ, ∃ s₀ : ℝ≥0, (s₀ : WithTop ℝ≥0) < F.zeta ω ∧
  ∀ (n : ℕ) (s : ℝ≥0), s₀ ≤ s → (s : WithTop ℝ≥0) ≤ F.e n ω → F.Sp n s ω < 1 / ((k : ℝ) + 1)

theorem e_le_zeta (n : ℕ) (ω : Ω₁) : F.e n ω ≤ F.zeta ω := le_iSup (fun n => F.e n ω) n

theorem Sp_eq_of_cons {ω : Ω₁} (h : F.IsCons ω) {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Sp n t ω = F.Sp m t ω := by
  simp only [Sp, Yf, (h n m hnm).2 t ht]

theorem Yf_eq_of_cons {ω : Ω₁} (h : F.IsCons ω) {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Yf n t ω = F.Yf m t ω := by
  simp only [Yf, (h n m hnm).2 t ht]

/-- On a consistent path with finite `ζ`, every `e_n` is strictly before `ζ`. -/
theorem e_lt_zeta {ω : Ω₁} (h : F.IsCons ω) (hζ : F.zeta ω < ⊤) (n : ℕ) :
    F.e n ω < F.zeta ω := by
  refine lt_of_le_of_ne (F.e_le_zeta n ω) fun heq => ?_
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hζ.ne
  obtain ⟨k, hk⟩ := exists_nat_ge (max (n : ℝ) ‖fromFlat z‖)
  have hnk : n ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
  have hek : ∀ j, n ≤ j → F.e j ω = m := fun j hj => le_antisymm (hm ▸ F.e_le_zeta j ω)
    (hm ▸ heq ▸ (h n j hj).1)
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ ‖F.X (k + 1) m ω‖ :=
    le_norm_exitTimeOf (F.continuous_X (k + 1) ω) (hek (k + 1) (by omega))
  have h2 : F.X k m ω = F.X (k + 1) m ω :=
    (h k (k + 1) (by omega)).2 m (by rw [hek k hnk])
  have h3 : ‖F.X k m ω‖ ≤ rad z k := F.norm_X_le k m ω
  have h4 : rad z k = k := max_eq_left ((le_max_right _ _).trans hk)
  rw [h2, h4] at h3
  push_cast at h1
  linarith

/-- On a consistent path, a hit of `{S ≤ ε}` before `e_n` is seen by all later paths. -/
theorem hitS_eq_of_cons {ω : Ω₁} (h : F.IsCons ω) {n m : ℕ} (hnm : n ≤ m) {ε : ℝ}
    (hle : F.hitS n ε ω ≤ F.e n ω) : F.hitS m ε ω = F.hitS n ε ω := by
  have hR : ∀ j t, Tendsto (fun u => F.Sp j u ω) (𝓝[≥] t) (𝓝 (F.Sp j t ω)) := fun j t =>
    tendsto_nhdsGE_of_continuous (F.continuous_Sp j ω) t
  apply le_antisymm
  · cases hτ : F.hitS n ε ω with
    | top => exact le_top
    | coe r =>
      have hr : F.Sp n r ω ≤ ε := hitLe_attained (hR n) hτ
      rw [F.Sp_eq_of_cons h hnm (hτ ▸ hle)] at hr
      exact iInf₂_le r hr
  · refine le_iInf₂ fun t ht => ?_
    by_cases htn : (t : WithTop ℝ≥0) ≤ F.e n ω
    · rw [← F.Sp_eq_of_cons h hnm htn] at ht
      exact iInf₂_le t ht
    · exact hle.trans (not_le.1 htn).le

/-- `S` comes back to `a` arbitrarily close to a finite `ζ < T`. -/
def Bad (a : ℝ) (T : ℕ) : Set Ω₁ :=
  {ω | F.IsCons ω ∧ F.zeta ω < (T : ℝ≥0) ∧ ∀ s₀ : ℝ≥0, (s₀ : WithTop ℝ≥0) < F.zeta ω →
    ∃ (n : ℕ) (s : ℝ≥0), s₀ ≤ s ∧ (s : WithTop ℝ≥0) ≤ F.e n ω ∧ a ≤ F.Sp n s ω}

/-- The paths that never reach `{S ≤ ε}` before their exit. -/
def NoHit (ε : ℝ) (T : ℕ) : Set Ω₁ :=
  {ω | ∀ n : ℕ, F.e n ω < F.hitS n ε ω ∧ F.e n ω < ((T : ℝ≥0) : WithTop ℝ≥0)}

/-- The `n`-th return event of estimate B. -/
def Up (n : ℕ) (ε a : ℝ) (T : ℕ) : Set Ω₁ :=
  {ω | F.hitS n ε ω < ((T : ℝ≥0) : WithTop ℝ≥0) ∧ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧
    F.hitS n ε ω ≤ s ∧ a ≤ F.Sp n s ω}

theorem bad_subset {a ε : ℝ} (T : ℕ) :
    F.Bad a T ⊆ F.NoHit ε T ∪ ⋃ N : ℕ, ⋂ n ∈ Ici N, F.Up n ε a T := by
  rintro ω ⟨hc, hζ, hB⟩
  by_cases hω : ω ∈ F.NoHit ε T
  · exact Or.inl hω
  right
  have hζ' : F.zeta ω < ⊤ := lt_of_lt_of_le hζ le_top
  simp only [NoHit, mem_ofPred_eq, not_forall] at hω
  obtain ⟨n₀, hn₀⟩ := hω
  have hen₀ : F.e n₀ ω < (T : ℝ≥0) := (F.e_le_zeta n₀ ω).trans_lt hζ
  have hhit : F.hitS n₀ ε ω ≤ F.e n₀ ω := by
    by_contra hc'; exact hn₀ ⟨not_le.1 hc', hen₀⟩
  have hlt : F.hitS n₀ ε ω < F.zeta ω := hhit.trans_lt (F.e_lt_zeta hc hζ' n₀)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  obtain ⟨n₁, s, hrs, hsn, has⟩ := hB r (hr ▸ hlt)
  refine mem_iUnion.2 ⟨max n₀ n₁, mem_iInter₂.2 fun n hn => ?_⟩
  have hn₀n : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁n : n₁ ≤ n := (le_max_right _ _).trans hn
  have hτ : F.hitS n ε ω = r := by rw [F.hitS_eq_of_cons hc hn₀n hhit, hr]
  have hsT : (s : WithTop ℝ≥0) < (T : ℝ≥0) := hsn.trans_lt ((F.e_le_zeta n₁ ω).trans_lt hζ)
  refine ⟨?_, s, (WithTop.coe_lt_coe.1 hsT).le, by rw [hτ]; exact WithTop.coe_le_coe.2 hrs, ?_⟩
  · rw [hτ]; exact (WithTop.coe_le_coe.2 hrs).trans_lt hsT
  · rwa [← F.Sp_eq_of_cons hc hn₁n hsn]

theorem measure_noHit (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (T : ℕ) : P₁ (F.NoHit ε T) = 0 := by
  have ha : 0 < exp (-D0 * (T : ℝ≥0)) * ε := mul_pos (exp_pos _) hε0
  refine eq_zero_of_forall_mul_le (measure_ne_top _ _) ha (D := lyapG z) fun M hM => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (1 + M)
  have h := F.measure_noHit_le hD0 hz n hε0 hε1 (T : ℝ≥0)
  calc P₁ (F.NoHit ε T) * ENNReal.ofReal (exp (-D0 * (T : ℝ≥0)) * ε * (1 + M))
      ≤ ENNReal.ofReal (exp (-D0 * (T : ℝ≥0)) * (ε * n)) *
        P₁ {ω | F.e n ω < F.hitS n ε ω ∧ F.e n ω < ((T : ℝ≥0) : WithTop ℝ≥0)} := by
        rw [mul_comm]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (measure_mono fun ω hω => hω n)
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hε0.le)
          (exp_pos _).le
    _ ≤ _ := h

theorem measure_liminf_up (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) {ε a : ℝ} (hε : 0 < ε)
    (ha : 0 < a) (T : ℕ) : P₁ (⋃ N : ℕ, ⋂ n ∈ Ici N, F.Up n ε a T) ≤ ENNReal.ofReal (ε / a) := by
  have hmono : Monotone fun N : ℕ => ⋂ n ∈ Ici N, F.Up n ε a T := fun N M hNM =>
    biInter_mono (Ici_subset_Ici.2 hNM) fun _ _ => le_rfl
  rw [hmono.measure_iUnion]
  refine iSup_le fun N => (measure_mono (biInter_subset_of_mem (mem_Ici.2 le_rfl))).trans ?_
  exact F.measure_upcross_le hD0 hz N hε ha (T : ℝ≥0)

theorem measure_bad (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (k T : ℕ) :
    P₁ (F.Bad (1 / ((k : ℝ) + 1)) T) = 0 := by
  set a : ℝ := 1 / ((k : ℝ) + 1) with hadef
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
  have hb : ∀ j : ℕ, P₁ (F.Bad a T) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := fun j => by
    set ε : ℝ := a / ((j : ℝ) + 2) with hεdef
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hεdef, div_le_one (by positivity)]; linarith [j.cast_nonneg (α := ℝ)]
    refine (measure_mono (F.bad_subset (ε := ε) T)).trans ((measure_union_le _ _).trans ?_)
    rw [F.measure_noHit hD0 hz hε hε1 T, zero_add]
    refine (F.measure_liminf_up hD0 hz hε ha T).trans (ENNReal.ofReal_le_ofReal ?_)
    have he : ε / a = 1 / ((j : ℝ) + 2) := by rw [hεdef]; field_simp
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_antisymm (ge_of_tendsto' ht hb) bot_le

/-- **The corner limit (pathwise form)**: almost surely the family is consistent and `S → 0`
at a finite `ζ`. -/
theorem ae_tendsto (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) :
    ∀ᵐ ω ∂P₁, F.IsCons ω ∧ F.IsConv ω := by
  have hnull : ∀ᵐ ω ∂P₁, ∀ k T : ℕ, ω ∉ F.Bad (1 / ((k : ℝ) + 1)) T := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro T
    exact measure_eq_zero_iff_ae_notMem.1 (F.measure_bad hD0 hz k T)
  filter_upwards [F.ae_consistent hD0, hnull] with ω hc hb
  refine ⟨hc, fun hζ k => ?_⟩
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hζ.ne
  obtain ⟨T, hT⟩ := exists_nat_gt (m : ℝ)
  have hζT : F.zeta ω < ((T : ℝ≥0) : WithTop ℝ≥0) := by
    rw [← hm]; exact WithTop.coe_lt_coe.2 (by exact_mod_cast hT)
  have h := hb k T
  simp only [Bad, mem_ofPred_eq, not_and, not_forall, not_exists, not_le] at h
  obtain ⟨s₀, hs₀, hS⟩ := h hc hζT
  exact ⟨s₀, hs₀, fun n s h1 h2 => hS n s h1 h2⟩

end SolFamily

end BlockBand.Transmission.Dual.Exists
