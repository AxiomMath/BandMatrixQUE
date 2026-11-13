module

public import BlockBand.Transmission.DualFeller.Glue

/-!
# The pathwise sandwich behind start continuity

Deterministic in `ω`. Two families `F, F'` (starts `ξ, ξ'`) on one driver space, a radius
`n ≥ ‖ξ‖, ‖ξ'‖`, a corner level `ε`, a return level `a`, a pair tolerance `r` such that
`pairDist < r` on the `n`-ball moves `π` by less than `min η (ε/2)` (`hmod`). At a path `ω` in
both `good₂` sets where
* (P) `pairDist(X_t, X'_t) < r` for `t ≤ T ∧ e_n ∧ e'_n`;
* (I) neither copy exits the `n`-ball before both its first hit of `{S ≤ ε}` and `T`;
* (U) no return to level `a` after the hits of `{S ≤ ε}` and `{S ≤ 2ε}` (`Ret`, both copies),
`pathwise` gives `‖Z̄_t − Z̄'_t‖ < η` for all `t ≤ T`, provided `2a ≤ η`.

Before the first hit `τ` of `{S ≤ ε}` by either copy, both are in the `n`-ball and (P) applies.
At `τ` the other copy has `S ≤ 2ε` (`after_hit`), so from `τ` on both `S` stay below `a` on
every radius, and `‖Z̄‖ ≤ S`; `Z̄ = 0` after `ζ`. No continuity of hitting times is used.
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
  {ξ ξ' : LΩ S → Fin 6 → ℝ}

theorem pairDist_comm (u v : Fin 6 → ℝ) : pairDist (u, v) = pairDist (v, u) := by
  unfold pairDist
  exact Finset.sum_congr rfl fun i _ => by ring

theorem le_e_of_noEsc (F : LiftFamily μ D0 ξ) {ω : LΩ S} {n : ℕ} {ε : ℝ} {T : ℝ≥0}
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T)) {t : ℝ≥0} (htT : t ≤ T)
    (hth : (t : WithTop ℝ≥0) ≤ F.hitS n ε ω) : (t : WithTop ℝ≥0) ≤ F.e n ω := by
  by_contra h
  have h' := not_le.1 h
  exact hI ⟨h'.trans_le hth, h'.trans_le (WithTop.coe_le_coe.2 htT)⟩

theorem tot_le_add (z z' : Fin 2 → ℝ) : tot z' ≤ tot z + 2 * ‖z - z'‖ := by
  have h0 := norm_le_pi_norm (z - z') 0
  have h1 := norm_le_pi_norm (z - z') 1
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h0 h1
  unfold tot
  linarith [neg_abs_le (z 0 - z' 0), neg_abs_le (z 1 - z' 1)]

/-- After the first hit of `{S ≤ ε}` (by `F`, the earlier one), both copies stay below `a`. -/
theorem after_hit (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') (hξ : IsLiftStart μ ξ)
    (hξ' : IsLiftStart μ ξ') {ω : LΩ S} (hω : ω ∈ F.good₂) (hω' : ω ∈ F'.good₂) {n : ℕ}
    {ε a r : ℝ} (ha : 0 < a) {T : ℝ≥0} (hn : ‖ξ ω‖ ≤ n) (hn' : ‖ξ' ω‖ ≤ n)
    (hmod : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ε / 2)
    (hP : ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
      pairDist (F.X n t ω, F'.X n t ω) < r)
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T))
    (hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T))
    (hle : F.hitS n ε ω ≤ F'.hitS n ε ω) (hR : ω ∉ Ret F n ε a T)
    (hR' : ω ∉ Ret F' n (2 * ε) a T) {t : ℝ≥0} (htT : t ≤ T) (hht : F.hitS n ε ω ≤ t) :
    ‖liftZbar F t ω‖ < a ∧ ‖liftZbar F' t ω‖ < a := by
  have hg := (F.good₂_spec hω).1
  have hg' := (F'.good₂_spec hω').1
  obtain ⟨h₀, hh₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hht)
  have h₀t : h₀ ≤ t := WithTop.coe_le_coe.1 (hh₀ ▸ hht)
  have h₀T : h₀ ≤ T := h₀t.trans htT
  have hhe : (h₀ : WithTop ℝ≥0) ≤ F.e n ω := le_e_of_noEsc F hI h₀T hh₀.le
  have hhe' : (h₀ : WithTop ℝ≥0) ≤ F'.e n ω := le_e_of_noEsc F' hI' h₀T (hh₀ ▸ hle)
  have hpd := hP h₀ h₀T (le_min hhe hhe')
  have hx : ‖F.X n h₀ ω‖ ≤ n := (F.norm_X_le n h₀ ω).trans (max_le le_rfl hn)
  have hx' : ‖F'.X n h₀ ω‖ ≤ n := (F'.norm_X_le n h₀ ω).trans (max_le le_rfl hn')
  have hπ := hmod _ _ hx hx' hpd
  have hRc : ∀ t, Tendsto (fun u => F.Sp n u ω) (𝓝[≥] t) (𝓝 (F.Sp n t ω)) := fun t =>
    SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t
  have hS₀ : F.Sp n h₀ ω ≤ ε := hitLe_attained hRc hh₀.symm
  have hS₀' : F'.Sp n h₀ ω ≤ 2 * ε := by
    have e1 : F.Sp n h₀ ω = tot (liftProj (F.X n h₀ ω)) := by
      simp only [LiftFamily.Sp, F.Yf_of_good hg, LiftFamily.Zp]
    have e2 : F'.Sp n h₀ ω = tot (liftProj (F'.X n h₀ ω)) := by
      simp only [LiftFamily.Sp, F'.Yf_of_good hg', LiftFamily.Zp]
    have := tot_le_add (liftProj (F.X n h₀ ω)) (liftProj (F'.X n h₀ ω))
    rw [e2]; rw [e1] at hS₀; linarith
  have hh' : F'.hitS n (2 * ε) ω ≤ t :=
    (iInf₂_le (f := fun s (_ : F'.Sp n s ω ≤ 2 * ε) => (s : WithTop ℝ≥0)) h₀ hS₀').trans
      (WithTop.coe_le_coe.2 h₀t)
  exact ⟨norm_liftZbar_lt F hξ hω ha (Sp_lt_of_not_ret F hg hR htT hht),
    norm_liftZbar_lt F' hξ' hω' ha (Sp_lt_of_not_ret F' hg' hR' htT hh')⟩

/-- **The pathwise sandwich.** -/
theorem pathwise (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') (hξ : IsLiftStart μ ξ)
    (hξ' : IsLiftStart μ ξ') {ω : LΩ S} (hω : ω ∈ F.good₂) (hω' : ω ∈ F'.good₂) {n : ℕ}
    {ε a r η : ℝ} (ha : 0 < a) (haη : 2 * a ≤ η) {T : ℝ≥0} (hn : ‖ξ ω‖ ≤ n)
    (hn' : ‖ξ' ω‖ ≤ n)
    (hmod : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < min η (ε / 2))
    (hP : ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
      pairDist (F.X n t ω, F'.X n t ω) < r)
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T))
    (hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T))
    (hR1 : ω ∉ Ret F n ε a T) (hR2 : ω ∉ Ret F n (2 * ε) a T)
    (hR1' : ω ∉ Ret F' n ε a T) (hR2' : ω ∉ Ret F' n (2 * ε) a T) :
    ∀ t : ℝ≥0, t ≤ T → ‖liftZbar F t ω - liftZbar F' t ω‖ < η := by
  intro t htT
  have hmod' : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ε / 2 := fun u v hu hv h =>
    (hmod u v hu hv h).trans_le (min_le_right _ _)
  by_cases h1 : (t : WithTop ℝ≥0) < F.hitS n ε ω ∧ (t : WithTop ℝ≥0) < F'.hitS n ε ω
  · have hte := le_e_of_noEsc F hI htT h1.1.le
    have hte' := le_e_of_noEsc F' hI' htT h1.2.le
    rw [liftZbar_eq F hω hte, liftZbar_eq F' hω' hte']
    exact (hmod _ _ ((F.norm_X_le n t ω).trans (max_le le_rfl hn))
      ((F'.norm_X_le n t ω).trans (max_le le_rfl hn')) (hP t htT (le_min hte hte'))).trans_le
      (min_le_left _ _)
  · rcases le_total (F.hitS n ε ω) (F'.hitS n ε ω) with hle | hle
    · have hht : F.hitS n ε ω ≤ t := by
        by_contra hc
        exact h1 ⟨not_le.1 hc, (not_le.1 hc).trans_le hle⟩
      obtain ⟨h₁, h₂⟩ := after_hit F F' hξ hξ' hω hω' ha hn hn' hmod' hP hI hI' hle hR1 hR2'
        htT hht
      exact (norm_sub_le _ _).trans_lt (by linarith)
    · have hht : F'.hitS n ε ω ≤ t := by
        by_contra hc
        exact h1 ⟨(not_le.1 hc).trans_le hle, not_le.1 hc⟩
      have hP' : ∀ s : ℝ≥0, s ≤ T → (s : WithTop ℝ≥0) ≤ min (F'.e n ω) (F.e n ω) →
          pairDist (F'.X n s ω, F.X n s ω) < r := fun s hs hse => by
        rw [pairDist_comm]; exact hP s hs (min_comm (F'.e n ω) (F.e n ω) ▸ hse)
      obtain ⟨h₁, h₂⟩ := after_hit F' F hξ' hξ hω' hω ha hn' hn hmod' hP' hI' hI hle hR1' hR2
        htT hht
      rw [norm_sub_rev]
      exact (norm_sub_le _ _).trans_lt (by linarith)

end BlockBand.Transmission.DualFeller
