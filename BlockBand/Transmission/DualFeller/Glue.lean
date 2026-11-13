module

public import BlockBand.Transmission.DualFeller.PairMax

/-!
# Pathwise facts on `Z̄` and the return events after the corner level

Setting: one lifted family `F`, start `ξ`. The corner is handled by exit levels, not by
continuity of hitting times.
* `liftZbar_eq`: on `good₂`, before the radius-`n` exit, `Z̄_t = π(X^n_t)`.
* `norm_liftZbar_lt`: on `good₂`, if `S^k_t < a` for every `k` with `t ≤ e_k`, then
  `‖Z̄_t‖ < a` (`Z̄_t = 0` after `ζ`).
* `Ret F n ε a T`: some `S^k` (`k ≥ n`) is `≥ a` at a time in `[hitS_n(ε), T]`.
  `Sp_lt_of_not_ret`: off `Ret`, `S^k_t < a` for all `k` and `t ∈ [hitS_n(ε), T]`, `t ≤ e_k`.
  `measure_ret_le`: on a start event inside `startBd B`, the paths with `hitS_n(ε) ≤ e_n` (or
  `e_n ≥ T`) in `Ret` have probability `≤ ε/a` (the no-return estimate `measure_liminf_up`,
  uniform in the radius; the radii are glued by consistency, as in `bad_subset`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ} (F : LiftFamily μ D0 ξ)

theorem norm_le_tot {z : Fin 2 → ℝ} (hz : z ∈ flatStrip) : ‖z‖ ≤ tot z := by
  refine (pi_norm_le_iff_of_nonneg (by unfold tot; linarith [hz.1, hz.2.1])).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp only [Fin.zero_eta, tot]; rw [abs_of_nonneg hz.1]; linarith [hz.2.1]
  · simp only [Fin.mk_one, tot]; rw [abs_of_nonneg hz.2.1]; linarith [hz.1]

theorem liftZbar_eq {ω : LΩ S} (hω : ω ∈ F.good₂) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : liftZbar F t ω = liftProj (F.X n t ω) := by
  have hg := (F.good₂_spec hω).1
  have hlt := F.lt_zeta_of_le_e hg ht
  have hN : F.N₂ t ω = 1 := by
    simp only [LiftFamily.N₂, hω, ite_true, LiftFamily.Nd, hg, true_and, not_le.2 hlt, ite_false]
  simp only [liftZbar, hN, ite_true, LiftFamily.Z₂, hω, LiftFamily.Zd, hg, F.Z_eq hg ht,
    F.Yf_of_good hg, LiftFamily.Zp]

theorem norm_liftZbar_lt (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good₂) {t : ℝ≥0} {a : ℝ}
    (ha : 0 < a) (hS : ∀ k : ℕ, (t : WithTop ℝ≥0) ≤ F.e k ω → F.Sp k t ω < a) :
    ‖liftZbar F t ω‖ < a := by
  have hg := (F.good₂_spec hω).1
  by_cases hlt : (t : WithTop ℝ≥0) < F.zeta ω
  · obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
    rw [liftZbar_eq F hω hk.le]
    change ‖F.Zp k t ω‖ < a
    rw [← F.Yf_of_good hg]
    exact (norm_le_tot (F.Yf_mem_strip hξ k t ω)).trans_lt (hS k hk.le)
  · have hN : F.N₂ t ω = 0 := by
      simp only [LiftFamily.N₂, hω, ite_true, LiftFamily.Nd, hg, true_and, not_lt.1 hlt,
        ite_true]
    simp only [liftZbar, hN, zero_ne_one, ite_false, norm_zero, ha]

/-- Return of some `S^k` (`k ≥ n`) to level `a` in `[hitS_n(ε), T]`. -/
def Ret (n : ℕ) (ε a : ℝ) (T : ℝ≥0) : Set (LΩ S) :=
  {ω | ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧ ∃ k : ℕ, n ≤ k ∧ (s : WithTop ℝ≥0) ≤ F.e k ω ∧
    a ≤ F.Sp k s ω}

theorem Sp_lt_of_not_ret {ω : LΩ S} (hg : ω ∈ F.good) {n : ℕ} {ε a : ℝ} {T : ℝ≥0}
    (hR : ω ∉ Ret F n ε a T) {t : ℝ≥0} (htT : t ≤ T) (hht : F.hitS n ε ω ≤ t) (k : ℕ)
    (hk : (t : WithTop ℝ≥0) ≤ F.e k ω) : F.Sp k t ω < a := by
  by_contra hge
  have hc := (F.good_spec hg).2 k (max k n) (le_max_left _ _)
  refine hR ⟨t, htT, hht, max k n, le_max_right _ _, hk.trans hc.1, ?_⟩
  rw [← F.Sp_eq_of_good hg (le_max_left _ _) hk]
  exact not_lt.1 hge

theorem measure_ret_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) {n : ℕ} {ε a : ℝ} (hε : 0 < ε)
    (hεa : ε < a) (T : ℝ≥0) {B : ℝ} {A : Set (LΩ S)}
    (hA : A ⊆ LiftFamily.startBd (ξ := ξ) B) :
    LP μ (A ∩ {ω | ω ∈ F.good ∧ ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T) ∧
      ω ∈ Ret F n ε a T}) ≤ ENNReal.ofReal (ε / a) := by
  have ha : 0 < a := hε.trans hεa
  refine le_trans (measure_mono ?_) (F.measure_liminf_up hD0 hξ hε ha ⌈(T : ℝ)⌉₊ B)
  rintro ω ⟨hωA, hg, hI, s, hsT, hhs, k₁, hnk, hse, has⟩
  refine ⟨hA hωA, ?_⟩
  have hTc : T ≤ ((⌈(T : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _
  have hhe : F.hitS n ε ω ≤ F.e n ω := by
    by_contra hc
    exact hI ⟨not_le.1 hc, (not_le.1 hc).trans_le (hhs.trans (WithTop.coe_le_coe.2 hsT))⟩
  obtain ⟨h₀, hh₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hhs)
  have hRc : ∀ t, Tendsto (fun u => F.Sp n u ω) (𝓝[≥] t) (𝓝 (F.Sp n t ω)) := fun t =>
    SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t
  have hS₀ : F.Sp n h₀ ω ≤ ε := hitLe_attained hRc hh₀.symm
  have hlt : F.hitS n ε ω < (T : WithTop ℝ≥0) := by
    rcases lt_or_eq_of_le (hhs.trans (WithTop.coe_le_coe.2 hsT)) with h | h
    · exact h
    · exfalso
      have hsT' : s = T := le_antisymm hsT (WithTop.coe_le_coe.1 (h ▸ hhs))
      have hh₀T : h₀ = T := WithTop.coe_injective (hh₀.trans h)
      have hTe : (s : WithTop ℝ≥0) ≤ F.e n ω := by rw [hsT', ← hh₀T, hh₀]; exact hhe
      rw [← F.Sp_eq_of_good hg hnk hTe, hsT', ← hh₀T] at has
      linarith
  refine mem_iUnion.2 ⟨k₁, mem_iInter₂.2 fun k hk => ?_⟩
  have hk₁k : k₁ ≤ k := hk
  have hτ : F.hitS k ε ω = F.hitS n ε ω := F.hitS_eq_of_good hg (hnk.trans hk₁k) hhe
  refine ⟨?_, s, hsT.trans hTc, by rw [hτ]; exact hhs, ?_⟩
  · rw [hτ]; exact hlt.trans_le (WithTop.coe_le_coe.2 hTc)
  · rwa [← F.Sp_eq_of_good hg hk₁k hse]

end BlockBand.Transmission.DualFeller
