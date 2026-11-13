module
public import BlockBand.SourceProcess.Stochastic.SDE
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Exit times of continuous paths

`exitTimeOf X R x = inf {t : R ≤ ‖X_t x‖}` (`⊤` if never; it agrees with `exitTime`,
`exitTimeOf_eq_exitTime`).
Pathwise facts (for a path `t ↦ X t x`, continuity assumed where stated):

* before the exit time `‖X_t‖ < R` (`norm_lt_of_lt_exitTimeOf`, no continuity);
* `exitTime ≤ t ↔ ∃ s ≤ t, R ≤ ‖X_s‖` (`exitTimeOf_le_iff`), the exit level is attained
  (`le_norm_exitTimeOf`), `‖X_s‖ ≤ R` for `0 < s ≤ exitTime` (`norm_le_of_le_exitTimeOf`);
* exit times increase to `⊤` with the radius (`tendsto_exitTimeOf_top`);
* the process stopped at its exit time has the same exit time (`exitTimeOf_stoppedProcess`).

Measurability (`isStoppingTime_exitTimeOf`): for any filtration `𝓕` on any measurable space,
the exit time of an `𝓕`-adapted process with **everywhere** continuous paths is an
`𝓕`-stopping time (`{exitTime ≤ t} = {R ≤ sup_{q ∈ ℚ} ‖X_{min(q⁺,t)}‖}`). For a.s.
continuous processes apply this to a continuous modification (augmented filtration).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E]

/-- Exit time of a general process (same formula as `Stochastic.exitTime`). -/
def exitTimeOf (X : ℝ≥0 → Ω → E) (R : ℝ) (x : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : R ≤ ‖X t x‖), (t : WithTop ℝ≥0)

theorem exitTimeOf_le {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω} {t : ℝ≥0} (h : R ≤ ‖X t x‖) :
    exitTimeOf X R x ≤ t :=
  iInf₂_le t h

theorem norm_lt_of_lt_exitTimeOf {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω} {t : ℝ≥0}
    (h : (t : WithTop ℝ≥0) < exitTimeOf X R x) : ‖X t x‖ < R := by
  by_contra hn
  exact absurd (exitTimeOf_le (le_of_not_gt hn)) (not_le.2 h)

theorem exitTimeOf_mono {X : ℝ≥0 → Ω → E} {R R' : ℝ} (hRR' : R ≤ R') (x : Ω) :
    exitTimeOf X R x ≤ exitTimeOf X R' x :=
  le_iInf₂ fun _ ht => exitTimeOf_le (hRR'.trans ht)

/-- Pathwise characterization of `{exitTime ≤ t}` for a continuous path. -/
theorem exitTimeOf_le_iff {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω}
    (hc : Continuous fun t => X t x) (t : ℝ≥0) :
    exitTimeOf X R x ≤ t ↔ ∃ s ≤ t, R ≤ ‖X s x‖ := by
  constructor
  · intro h
    by_contra hn
    simp only [not_exists, not_and, not_le] at hn
    set A : Set ℝ≥0 := {s | R ≤ ‖X s x‖}
    have hA : IsClosed A := isClosed_le continuous_const (continuous_norm.comp hc)
    rcases A.eq_empty_or_nonempty with hAe | hAne
    · have htop : exitTimeOf X R x = ⊤ := by
        refine le_antisymm le_top (le_iInf₂ fun s hs => ?_)
        exact absurd (show s ∈ A from hs) (by rw [hAe]; exact notMem_empty s)
      rw [htop] at h
      exact WithTop.coe_ne_top (top_le_iff.1 h)
    · have hm : sInf A ∈ A := hA.csInf_mem hAne ⟨0, fun _ _ => zero_le⟩
      have hmt : t < sInf A := by
        by_contra hle
        exact absurd (hn (sInf A) (le_of_not_gt hle)) (not_lt.2 hm)
      have hge : ((sInf A : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeOf X R x :=
        le_iInf₂ fun s hs => WithTop.coe_le_coe.2 (csInf_le ⟨0, fun _ _ => zero_le⟩ hs)
      exact absurd (hge.trans h) (not_le.2 (WithTop.coe_lt_coe.2 hmt))
  · rintro ⟨s, hst, hs⟩
    exact (exitTimeOf_le hs).trans (WithTop.coe_le_coe.2 hst)

/-- At a finite exit time the exit level is attained. -/
theorem le_norm_exitTimeOf {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω}
    (hc : Continuous fun t => X t x) {m : ℝ≥0} (hm : exitTimeOf X R x = m) :
    R ≤ ‖X m x‖ := by
  obtain ⟨s, hsm, hs⟩ := (exitTimeOf_le_iff hc m).1 hm.le
  have hms : m ≤ s := by
    have := exitTimeOf_le (X := X) (x := x) hs
    rw [hm] at this
    exact WithTop.coe_le_coe.1 this
  rwa [le_antisymm hsm hms] at hs

/-- Up to (and including) a positive time not after the exit time, `‖X_s‖ ≤ R`. -/
theorem norm_le_of_le_exitTimeOf {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω}
    (hc : Continuous fun t => X t x) {s : ℝ≥0} (hs0 : 0 < s)
    (hs : (s : WithTop ℝ≥0) ≤ exitTimeOf X R x) : ‖X s x‖ ≤ R := by
  have hC : IsClosed {r : ℝ≥0 | ‖X r x‖ ≤ R} := isClosed_le (continuous_norm.comp hc) continuous_const
  have hsub : Iio s ⊆ {r : ℝ≥0 | ‖X r x‖ ≤ R} := fun r hr =>
    (norm_lt_of_lt_exitTimeOf (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hr) hs)).le
  have hcl := hC.closure_subset_iff.2 hsub
  rw [closure_Iio' (a := s) ⟨0, hs0⟩] at hcl
  exact hcl (le_refl s)

/-- Exit times from growing balls increase to `⊤` along a continuous path. -/
theorem tendsto_exitTimeOf_top {X : ℝ≥0 → Ω → E} {x : Ω} (hc : Continuous fun t => X t x) :
    Tendsto (fun n : ℕ => exitTimeOf X n x) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro i
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := i)).exists_bound_of_continuousOn
    hc.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop n] with k hk
  by_contra hle
  obtain ⟨s, hsi, hs⟩ := (exitTimeOf_le_iff hc i).1 (le_of_not_gt hle)
  have h1 := hM s ⟨zero_le, hsi⟩
  have h2 : (n : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The process stopped at its own exit time has the same exit time. -/
theorem exitTimeOf_stoppedProcess {X : ℝ≥0 → Ω → E} {R : ℝ} {x : Ω}
    (hc : Continuous fun t => X t x) :
    exitTimeOf (stoppedProcess X (exitTimeOf X R)) R x = exitTimeOf X R x := by
  apply le_antisymm
  · cases he : exitTimeOf X R x with
    | top => exact le_top
    | coe m =>
      apply exitTimeOf_le
      rw [stoppedProcess_eq_of_le (by rw [he])]
      exact le_norm_exitTimeOf hc he
  · refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    rw [not_le] at hlt
    rw [stoppedProcess_eq_of_le hlt.le] at ht
    exact absurd (norm_lt_of_lt_exitTimeOf hlt) (not_lt.2 ht)

theorem continuous_stoppedProcess {X : ℝ≥0 → Ω → E} {x : Ω} (hc : Continuous fun t => X t x)
    (τ : Ω → WithTop ℝ≥0) : Continuous fun t => stoppedProcess X τ t x := by
  cases hτ : τ x with
  | top =>
    have : (fun t => stoppedProcess X τ t x) = fun t => X t x := by
      funext t
      exact stoppedProcess_eq_of_le (by rw [hτ]; exact le_top)
    rw [this]
    exact hc
  | coe m =>
    have : (fun t => stoppedProcess X τ t x) = fun t => X (min t m) x := by
      funext t
      simp only [stoppedProcess, hτ]
      rw [← WithTop.coe_min]
      exact congrArg (fun r => X r x) (WithTop.untopD_coe _ _)
    rw [this]
    exact hc.comp (continuous_id.min continuous_const)

theorem exitTimeOf_eq_exitTime {S κ : Type*} {E : Type*} [NormedAddCommGroup E]
    (X : ℝ≥0 → FiniteDriverIntegration.DriverSample S κ → E) (R : ℝ) :
    exitTimeOf X R = exitTime X R := rfl

section Measurability

variable [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]

/-- **Exit times of continuous adapted processes are stopping times.** -/
theorem isStoppingTime_exitTimeOf {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → E} (hX : ∀ t, StronglyMeasurable[𝓕 t] (X t))
    (hc : ∀ x, Continuous fun t => X t x) (R : ℝ) : IsStoppingTime 𝓕 (exitTimeOf X R) := by
  intro t
  let c : ℚ → ℝ≥0 := fun q => min (q : ℝ).toNNReal t
  let F : Ω → ℝ≥0∞ := fun x => ⨆ q : ℚ, ‖X (c q) x‖ₑ
  have hF : Measurable[𝓕 t] F := by
    let _ : MeasurableSpace Ω := 𝓕 t
    refine Measurable.iSup fun q => ?_
    exact (((hX (c q)).mono (𝓕.mono (min_le_right _ _))).measurable).enorm
  have hset : {x | exitTimeOf X R x ≤ t} = {x | ENNReal.ofReal R ≤ F x} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [exitTimeOf_le_iff (hc x)]
    constructor
    · rintro ⟨s, hst, hs⟩
      have hcont : Continuous fun r : ℝ => ‖X (min r.toNNReal t) x‖ₑ :=
        continuous_enorm.comp ((hc x).comp (continuous_real_toNNReal.min continuous_const))
      have hle : ‖X (min (s : ℝ).toNNReal t) x‖ₑ ≤ F x := by
        refine Rat.denseRange_cast.induction_on (p := fun r : ℝ => ‖X (min r.toNNReal t) x‖ₑ ≤ F x)
          (s : ℝ) (isClosed_le hcont continuous_const) fun q => ?_
        exact le_iSup (fun q : ℚ => ‖X (c q) x‖ₑ) q
      rw [Real.toNNReal_coe, min_eq_left hst] at hle
      refine le_trans ?_ hle
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hs
    · intro h
      obtain ⟨s, hs, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMaxOn
        (nonempty_Icc.2 zero_le) (continuous_norm.comp (hc x)).continuousOn
      refine ⟨s, hs.2, ?_⟩
      have hFle : F x ≤ ‖X s x‖ₑ := iSup_le fun q => by
        have hq := hmax (show c q ∈ Icc (0 : ℝ≥0) t from ⟨zero_le, min_le_right _ _⟩)
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hq
      have := h.trans hFle
      rw [← ofReal_norm] at this
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).1 this
  rw [hset]
  exact measurableSet_le measurable_const hF

end Measurability

end BlockBand.SourceProcess.Stochastic.NativeSDE
