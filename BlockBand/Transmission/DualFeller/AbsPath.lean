module

public import BlockBand.Transmission.DualFeller.AbsorbEvent

/-!
# The pathwise sandwich behind corner absorption

Deterministic in `ω`. Two families `F, F'` (starts `ξ, ξ'`) on one driver space, a radius
`n ≥ ‖ξ‖, ‖ξ'‖`, a corner level `ε ≥ 0` and a pair tolerance `r` such that `pairDist < r` on the
`n`-ball moves `π` by less than `ε/2` (`hmod`). At a path `ω` in both `good` sets where
* (P) `pairDist(X_t, X'_t) < r` for `t ≤ T ∧ e_n ∧ e'_n`;
* (I) neither copy exits the `n`-ball before both its first hit of `{S ≤ ε}` and `T`;
* (A) `ζ ∧ T − hitS_n(2ε) ∧ T < η` for both copies,
`abs_sub_zeta_lt` gives `|ζ ∧ T − ζ' ∧ T| < η`.

Let `h ≤ h'` be the hits of `{S ≤ ε}`. If `h ≥ T`, both copies live until `T` by (I).
Otherwise both `ζ ∧ T` and `ζ' ∧ T` lie in `[h, T]` (by (I), `ζ ≥ e_n ≥ h`), and at `h` the
other copy has `S' ≤ 2ε` (`hitS_two_le`, from (P)), so `hitS_n(2ε) ≤ h` for both copies; (A)
then puts both in `[h, h + η)`. No continuity of hitting times is used.
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

theorem hitS_mono (F : LiftFamily μ D0 ξ) (n : ℕ) {ε ε' : ℝ} (h : ε ≤ ε') (ω : LΩ S) :
    F.hitS n ε' ω ≤ F.hitS n ε ω := by
  unfold LiftFamily.hitS hitLe
  exact le_iInf₂ fun s hs => iInf₂_le s (hs.trans h)

/-- At the first hit `h₀ < T` of `{S ≤ ε}` by `F`, the other copy has `S' ≤ 2ε`. -/
theorem hitS_two_le (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') {ω : LΩ S}
    (hg : ω ∈ F.good) (hg' : ω ∈ F'.good) {n : ℕ} {ε r : ℝ} {T : ℝ≥0} (hn : ‖ξ ω‖ ≤ n)
    (hn' : ‖ξ' ω‖ ≤ n)
    (hmod : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ε / 2)
    (hP : ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
      pairDist (F.X n t ω, F'.X n t ω) < r)
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T))
    (hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T))
    (hle : F.hitS n ε ω ≤ F'.hitS n ε ω) {h₀ : ℝ≥0} (hh₀ : F.hitS n ε ω = h₀) (h₀T : h₀ ≤ T) :
    F'.hitS n (2 * ε) ω ≤ h₀ := by
  have hhe : (h₀ : WithTop ℝ≥0) ≤ F.e n ω := le_e_of_noEsc F hI h₀T hh₀.ge
  have hhe' : (h₀ : WithTop ℝ≥0) ≤ F'.e n ω := le_e_of_noEsc F' hI' h₀T (hh₀.ge.trans hle)
  have hpd := hP h₀ h₀T (le_min hhe hhe')
  have hx : ‖F.X n h₀ ω‖ ≤ n := (F.norm_X_le n h₀ ω).trans (max_le le_rfl hn)
  have hx' : ‖F'.X n h₀ ω‖ ≤ n := (F'.norm_X_le n h₀ ω).trans (max_le le_rfl hn')
  have hπ := hmod _ _ hx hx' hpd
  have hRc : ∀ t, Tendsto (fun u => F.Sp n u ω) (𝓝[≥] t) (𝓝 (F.Sp n t ω)) := fun t =>
    SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t
  have hS₀ : F.Sp n h₀ ω ≤ ε := hitLe_attained hRc hh₀
  have e1 : F.Sp n h₀ ω = tot (liftProj (F.X n h₀ ω)) := by
    simp only [LiftFamily.Sp, F.Yf_of_good hg, LiftFamily.Zp]
  have e2 : F'.Sp n h₀ ω = tot (liftProj (F'.X n h₀ ω)) := by
    simp only [LiftFamily.Sp, F'.Yf_of_good hg', LiftFamily.Zp]
  have := tot_le_add (liftProj (F.X n h₀ ω)) (liftProj (F'.X n h₀ ω))
  have hS₀' : F'.Sp n h₀ ω ≤ 2 * ε := by rw [e2]; rw [e1] at hS₀; linarith
  exact iInf₂_le (f := fun s (_ : F'.Sp n s ω ≤ 2 * ε) => (s : WithTop ℝ≥0)) h₀ hS₀'

theorem untopA_min_zeta_ge (F : LiftFamily μ D0 ξ) {n : ℕ} {ω : LΩ S} {T h₀ : ℝ≥0}
    (h₀T : h₀ ≤ T) (he : (h₀ : WithTop ℝ≥0) ≤ F.e n ω) :
    (h₀ : ℝ) ≤ (((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) :=
  le_untopA_of_le h₀T (he.trans (F.e_le_zeta n ω))

theorem absStart_le_of_hit (F : LiftFamily μ D0 ξ) {n : ℕ} {ε : ℝ} {ω : LΩ S} {T h₀ : ℝ≥0}
    (h₀T : h₀ ≤ T) (hh : F.hitS n ε ω ≤ h₀) : absStart F n ε T ω ≤ h₀ := by
  have := untopA_min_mono T hh
  rwa [min_eq_right (WithTop.coe_le_coe.2 h₀T), untopA_ofNN] at this

/-- **The sandwich**, when `F` hits `{S ≤ ε}` first. -/
theorem abs_sub_zeta_lt_of_le (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') {ω : LΩ S}
    (hg : ω ∈ F.good) (hg' : ω ∈ F'.good) {n : ℕ} {ε r η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    {T : ℝ≥0} (hn : ‖ξ ω‖ ≤ n) (hn' : ‖ξ' ω‖ ≤ n)
    (hmod : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ε / 2)
    (hP : ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
      pairDist (F.X n t ω, F'.X n t ω) < r)
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T))
    (hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T))
    (hle : F.hitS n ε ω ≤ F'.hitS n ε ω)
    (hA : (((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
      absStart F n (2 * ε) T ω < η)
    (hA' : (((min (T : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ) -
      absStart F' n (2 * ε) T ω < η) :
    |(((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
      (((min (T : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ)| < η := by
  have hz := untopA_min_le T (F.zeta ω)
  have hz' := untopA_min_le T (F'.zeta ω)
  rcases le_or_gt (T : WithTop ℝ≥0) (F.hitS n ε ω) with hT | hT
  · -- no hit before `T`: both copies live until `T`
    have he : (T : WithTop ℝ≥0) ≤ F.e n ω := not_lt.1 fun h => hI ⟨h.trans_le hT, h⟩
    have he' : (T : WithTop ℝ≥0) ≤ F'.e n ω := not_lt.1 fun h => hI' ⟨h.trans_le (hT.trans hle), h⟩
    have h1 := untopA_min_zeta_ge F le_rfl he
    have h2 := untopA_min_zeta_ge F' le_rfl he'
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  · obtain ⟨h₀, hh₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hT)
    have h₀T : h₀ ≤ T := (WithTop.coe_lt_coe.1 (hh₀ ▸ hT)).le
    have hhe : (h₀ : WithTop ℝ≥0) ≤ F.e n ω := le_e_of_noEsc F hI h₀T hh₀.le
    have hhe' : (h₀ : WithTop ℝ≥0) ≤ F'.e n ω := le_e_of_noEsc F' hI' h₀T (hh₀.le.trans hle)
    have h1 := untopA_min_zeta_ge F h₀T hhe
    have h2 := untopA_min_zeta_ge F' h₀T hhe'
    have h3 : absStart F n (2 * ε) T ω ≤ h₀ :=
      absStart_le_of_hit F h₀T ((hitS_mono F n (by linarith) ω).trans hh₀.symm.le)
    have h4 : absStart F' n (2 * ε) T ω ≤ h₀ :=
      absStart_le_of_hit F' h₀T (hitS_two_le F F' hg hg' hn hn' hmod hP hI hI' hle hh₀.symm h₀T)
    rw [abs_sub_lt_iff]
    constructor <;> linarith

/-- **The sandwich.** -/
theorem abs_sub_zeta_lt (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') {ω : LΩ S}
    (hg : ω ∈ F.good) (hg' : ω ∈ F'.good) {n : ℕ} {ε r η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    {T : ℝ≥0} (hn : ‖ξ ω‖ ≤ n) (hn' : ‖ξ' ω‖ ≤ n)
    (hmod : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
      ‖liftProj u - liftProj v‖ < ε / 2)
    (hP : ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
      pairDist (F.X n t ω, F'.X n t ω) < r)
    (hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T))
    (hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T))
    (hA : (((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
      absStart F n (2 * ε) T ω < η)
    (hA' : (((min (T : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ) -
      absStart F' n (2 * ε) T ω < η) :
    |(((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
      (((min (T : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ)| < η := by
  rcases le_total (F.hitS n ε ω) (F'.hitS n ε ω) with hle | hle
  · exact abs_sub_zeta_lt_of_le F F' hg hg' hε hη hn hn' hmod hP hI hI' hle hA hA'
  · have hmod' : ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ n → ‖v‖ ≤ n → pairDist (u, v) < r →
        ‖liftProj u - liftProj v‖ < ε / 2 := fun u v hu hv h => by
      rw [norm_sub_rev]; exact hmod v u hv hu (by rwa [pairDist_comm])
    have hP' : ∀ s : ℝ≥0, s ≤ T → (s : WithTop ℝ≥0) ≤ min (F'.e n ω) (F.e n ω) →
        pairDist (F'.X n s ω, F.X n s ω) < r := fun s hs hse => by
      rw [pairDist_comm]; exact hP s hs (min_comm (F'.e n ω) (F.e n ω) ▸ hse)
    rw [abs_sub_comm]
    exact abs_sub_zeta_lt_of_le F' F hg' hg hε hη hn' hn hmod' hP' hI' hI hle hA' hA

end BlockBand.Transmission.DualFeller
