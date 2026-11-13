module

public import BlockBand.SourceProcess.ComplexUnique.Bounds

/-!
# Localization for the restart of a localized complex martingale problem

`hitK X k = rawHit {‖x‖ ≥ k} X` (a stopping time) and the `𝓖_a`-events
`evK X a k = {a < hitK X k}`:
* `continuous_lComp`, `continuous_lBr`, `continuous_lBr'`: the clause processes have continuous
  paths (the integrands are bounded measurable along the path);
* `eventually_mem_evK`: a.s. eventually `ω ∈ evK X a k`;
* `add_exit_le_hitK`: on `evK X a k`, for `k` above the size of the restarted path in `W`,
  `a + (exit of the restarted path from W) ≤ hitK X k`;
* `exists_bound_lComp`: a bound for `lComp_p(a)` on `evK X a k`. With it, the sibling module
  `BridgeMain` constructs a bounded `𝓖_a`-measurable version of `1_{evK} lComp_p(a)`
  (`exists_factor`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornRestart
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*} {X : ℝ≥0 → Ω → κ → ℂ} {c : ℝ≥0 → κ → ℂ} {ω : Ω}

/-- The localizing hit `θ_k` of `{‖x‖ ≥ k}`. -/
def hitK (X : ℝ≥0 → Ω → κ → ℂ) (k : ℕ) : Ω → WithTop ℝ≥0 :=
  rawHit {x : κ → ℂ | (k : ℝ) ≤ ‖x‖} X

/-- The `𝓖_a`-event `{a < θ_k}`. -/
def evK (X : ℝ≥0 → Ω → κ → ℂ) (a : ℝ≥0) (k : ℕ) : Set Ω := {ω | (a : WithTop ℝ≥0) < hitK X k ω}

theorem isClosed_normGe (k : ℝ) : IsClosed {x : κ → ℂ | k ≤ ‖x‖} :=
  isClosed_le continuous_const continuous_norm

theorem hitK_eq (hx : Continuous fun t => X t ω) (k : ℕ) :
    hitK X k ω = hitTime {x : κ → ℂ | (k : ℝ) ≤ ‖x‖} X ω :=
  rawHit_eq_hitTime (isClosed_normGe _) hx

theorem norm_lt_of_lt_hitK (hx : Continuous fun t => X t ω) {k : ℕ} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < hitK X k ω) : ‖X s ω‖ < k := by
  rw [hitK_eq hx] at hs
  by_contra h
  exact absurd (iInf₂_le s (show (k : ℝ) ≤ ‖X s ω‖ from not_lt.1 h)) (not_le.2 hs)

theorem eventually_mem_evK (hx : Continuous fun t => X t ω) (a : ℝ≥0) :
    ∀ᶠ k : ℕ in atTop, ω ∈ evK X a k := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a + 1)).exists_bound_of_continuousOn
    hx.continuousOn
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop R] with k hk
  show (a : WithTop ℝ≥0) < hitK X k ω
  rw [hitK_eq hx]
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one a)) (le_iInf₂ fun t ht => ?_)
  refine WithTop.coe_le_coe.2 (not_lt.1 fun h => ?_)
  have := hR t ⟨zero_le, h.le⟩
  simp only [mem_ofPred_eq] at ht this
  linarith

section Meas
variable {m : MeasurableSpace Ω} [MeasurableSpace (κ → ℂ)] [BorelSpace (κ → ℂ)]

theorem isStoppingTime_hitK {𝓖 : Filtration ℝ≥0 m} (hX : ∀ t, Measurable[𝓖 t] (X t)) (k : ℕ) :
    IsStoppingTime 𝓖 (hitK X k) :=
  isStoppingTime_rawHit hX

theorem measurableSet_evK {𝓖 : Filtration ℝ≥0 m} (hX : ∀ t, Measurable[𝓖 t] (X t)) (a : ℝ≥0)
    (k : ℕ) : MeasurableSet[𝓖 a] (evK X a k) := by
  have h := (isStoppingTime_hitK hX k) a
  have e : evK X a k = {ω | hitK X k ω ≤ a}ᶜ := by ext ω; simp [evK]; exact not_le.symm
  rw [e]; exact h.compl

end Meas

theorem tsub_lt_of_lt_add {a t : ℝ≥0} {θ : WithTop ℝ≥0} (hat : a ≤ t)
    (h : (t : WithTop ℝ≥0) < (a : WithTop ℝ≥0) + θ) : ((t - a : ℝ≥0) : WithTop ℝ≥0) < θ := by
  induction θ with
  | top => exact WithTop.coe_lt_top _
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_lt_coe] at h
    exact WithTop.coe_lt_coe.2 ((tsub_lt_iff_left hat).2 h)

/-- **Before the restarted exit, the continuous part stays below level `k`.** -/
theorem add_exit_le_hitK (hx : Continuous fun t => X t ω) {a h : ℝ≥0}
    {W : Set (Fin (rDim κ) → ℝ)} (hWU : W ⊆ {y | tOf y < h}) {Rz C : ℝ}
    (hRz : ∀ y ∈ W, ‖zOf y‖ ≤ Rz) (hC : ‖c a‖ ≤ C) {k : ℕ} (hk : Rz + C < k)
    (hω : ω ∈ evK X a k) :
    (a : WithTop ℝ≥0) + exitTimeFrom W (rsY X c a h) ω ≤ hitK X k ω := by
  rw [hitK_eq hx]
  refine le_iInf₂ fun t ht => ?_
  by_contra hlt
  push Not at hlt
  have hat : (a : WithTop ℝ≥0) < t := lt_of_lt_of_le hω (by rw [hitK_eq hx]; exact iInf₂_le t ht)
  have hat' : a ≤ t := (WithTop.coe_lt_coe.1 hat).le
  have hs := tsub_lt_of_lt_add hat' hlt
  have hY := mem_of_lt_exitTimeFrom hs
  have hth : tOf (rsY X c a h (t - a) ω) < h := hWU hY
  rw [tOf_rsY] at hth
  have hsh : t - a < h := by
    by_contra h'; push Not at h'
    rw [min_eq_right h'] at hth; exact lt_irrefl _ hth
  have hz := hRz _ hY
  rw [zOf_rsY, min_eq_left hsh.le, add_tsub_cancel_of_le hat'] at hz
  have h1 : ‖X t ω‖ ≤ Rz + C := by
    have := norm_sub_le (X t ω + c a) (c a)
    rw [add_sub_cancel_right] at this
    linarith
  simp only [mem_ofPred_eq] at ht
  linarith

theorem continuous_intIoc {f : ℝ → ℂ} (hf : ∀ A B : ℝ, IntervalIntegrable f volume A B) :
    Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, f s := by
  have e : (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, f s) =
      (fun b : ℝ => ∫ s in (0 : ℝ)..b, f s) ∘ (fun t : ℝ≥0 => (t : ℝ)) := by
    funext t; simp only [Function.comp, intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  rw [e]
  exact (intervalIntegral.continuous_primitive hf 0).comp NNReal.continuous_coe

variable {β : (κ → ℂ) → κ → ℂ} {Γ : (κ → ℂ) → κ → κ → ℂ}

theorem continuous_lComp (hβ : Continuous β) (hx : Continuous fun t => X t ω) (hc : Measurable c)
    {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (p : κ) : Continuous fun t => lComp β c X p t ω :=
  ((((continuous_apply p).comp hx).sub continuous_const)).sub
    (continuous_intIoc (intervalIntegrable_comp_add ((continuous_apply p).comp hβ) hx hc hC))

theorem continuous_lBr (hβ : Continuous β) (hΓ : Continuous Γ) (hx : Continuous fun t => X t ω)
    (hc : Measurable c) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (p q : κ) :
    Continuous fun t => lBr β Γ c X p q t ω :=
  ((continuous_lComp hβ hx hc hC p).mul (continuous_lComp hβ hx hc hC q)).sub
    (continuous_intIoc (intervalIntegrable_comp_add
      ((continuous_apply q).comp ((continuous_apply p).comp hΓ)) hx hc hC))

theorem continuous_lBr' (hβ : Continuous β) (hΓ : Continuous Γ) (hx : Continuous fun t => X t ω)
    (hc : Measurable c) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (p q : κ) :
    Continuous fun t => lBr' β Γ c X p q t ω :=
  ((continuous_lComp hβ hx hc hC p).mul (continuous_lComp hβ hx hc hC q).star).sub
    (continuous_intIoc (intervalIntegrable_comp_add
      ((continuous_apply q).comp ((continuous_apply p).comp hΓ)) hx hc hC))

/-- A bound for `lComp_p(a)` on `evK X a k`. -/
theorem exists_bound_lComp (hβ : Continuous β) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (a : ℝ≥0) (k : ℕ) :
    ∃ B, ∀ ω, Continuous (fun t => X t ω) → ω ∈ evK X a k → ∀ p, ‖lComp β c X p a ω‖ ≤ B := by
  obtain ⟨Bβ, hBβ⟩ := (isCompact_closedBall (0 : κ → ℂ) (k + C)).exists_bound_of_continuousOn
    hβ.continuousOn
  refine ⟨k + k + max Bβ 0 * a, fun ω hx hω p => ?_⟩
  have hs : ∀ s ≤ a, ‖X s ω‖ < k := fun s hs =>
    norm_lt_of_lt_hitK hx (lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) hω)
  have hi := norm_setIntegral_Ioc_le (f := fun s => β (X s ω + c s) p) (le_max_right Bβ 0)
    (le_refl a) fun s hs' => by
      refine (norm_le_pi_norm _ p).trans ((hBβ _ ?_).trans (le_max_left _ _))
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_add_le _ _).trans (add_le_add (hs s hs').le (hC s))
  unfold lComp
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) hi)
  · exact (norm_le_pi_norm _ p).trans (hs a le_rfl).le
  · exact (norm_le_pi_norm _ p).trans (hs 0 zero_le).le

end BlockBand.SourceProcess.ComplexUnique
