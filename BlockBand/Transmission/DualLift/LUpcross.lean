module

public import BlockBand.Transmission.DualLift.LBoundary

/-!
# No return from `{S ≤ ε}` to `{S ≥ a}` along the lift

The upcrossing estimate of the dual process, with the measure restricted to an event
`A ∈ L𝓖 μ 0`.

`measure_upcross_le`: if `S(π ξ) ≤ B` on `A`, then
`P(A ∩ {hitS n ε < T, ∃ s ∈ [hitS n ε, T], S(Yf n s) ≥ a}) ≤ ε/a` (`ε, a > 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- `−S` after `hitS n ε`, `0` before. -/
def postV (n : ℕ) (ε : ℝ) (t : ℝ≥0) (ω : LΩ S) : ℝ :=
  if F.hitS n ε ω ≤ t then -F.Sp n t ω else 0

/-- The first time at or after `hitS n ε` with `S ≥ a`. -/
def hitUp (n : ℕ) (ε a : ℝ) : LΩ S → WithTop ℝ≥0 := hitLe (F.postV n ε) (-a)

theorem postV_of_le (n : ℕ) (ε : ℝ) {t : ℝ≥0} {ω : LΩ S} (h : F.hitS n ε ω ≤ t) :
    F.postV n ε t ω = -F.Sp n t ω := ite_eq_left h

theorem postV_of_lt (n : ℕ) (ε : ℝ) {t : ℝ≥0} {ω : LΩ S}
    (h : (t : WithTop ℝ≥0) < F.hitS n ε ω) : F.postV n ε t ω = 0 := ite_eq_right (not_le.2 h)

theorem postV_rightCont (n : ℕ) (ε : ℝ) (ω : LΩ S) (t : ℝ≥0) :
    Tendsto (fun u => F.postV n ε u ω) (𝓝[≥] t) (𝓝 (F.postV n ε t ω)) := by
  by_cases h : F.hitS n ε ω ≤ t
  · have he : (fun u => F.postV n ε u ω) =ᶠ[𝓝[≥] t] fun u => -F.Sp n u ω :=
      eventually_nhdsWithin_of_forall fun u hu =>
        F.postV_of_le n ε (h.trans (WithTop.coe_le_coe.2 hu))
    rw [F.postV_of_le n ε h]
    exact (SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω).neg t).congr' he.symm
  · have hlt : (t : WithTop ℝ≥0) < F.hitS n ε ω := not_le.1 h
    have he : (fun u => F.postV n ε u ω) =ᶠ[𝓝 t] fun _ => F.postV n ε t ω := by
      filter_upwards [(isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt] with u hu
      rw [F.postV_of_lt n ε hu, F.postV_of_lt n ε hlt]
    exact tendsto_const_nhds.congr' (he.filter_mono nhdsWithin_le_nhds).symm

theorem postV_lsc (hξ : IsLiftStart μ ξ) (n : ℕ) (ε : ℝ) (ω : LΩ S) :
    LowerSemicontinuous fun u => F.postV n ε u ω := by
  intro t y hy
  have hy' : y < F.postV n ε t ω := hy
  show ∀ᶠ u in 𝓝 t, y < F.postV n ε u ω
  by_cases h : F.hitS n ε ω ≤ t
  · rw [F.postV_of_le n ε h] at hy'
    have h0 : y < 0 := hy'.trans (neg_lt_zero.2 (F.Sp_pos hξ n t ω))
    filter_upwards [((F.continuous_Sp n ω).neg.continuousAt (x := t)).eventually
      (lt_mem_nhds hy')] with u hu
    by_cases hu' : F.hitS n ε ω ≤ u
    · rw [F.postV_of_le n ε hu']; exact hu
    · rw [F.postV_of_lt n ε (not_le.1 hu')]; exact h0
  · have hlt : (t : WithTop ℝ≥0) < F.hitS n ε ω := not_le.1 h
    rw [F.postV_of_lt n ε hlt] at hy'
    filter_upwards [(isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt] with u hu
    rw [F.postV_of_lt n ε hu]; exact hy'

theorem isStoppingTime_hitUp (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) (ε a : ℝ) :
    IsStoppingTime (L𝓖 μ) (F.hitUp n ε a) :=
  isStoppingTime_hitLe (fun t => Measurable.ite
    ((F.isStoppingTime_hitS hD0 hξ n ε).measurableSet_le t)
    (F.measurable_Sp hD0 hξ n t).neg measurable_const) (fun ω t => F.postV_rightCont n ε ω t)
    (F.postV_lsc hξ n ε) (-a)

/-- **Estimate B**, on a `𝓖₀`-event. -/
theorem measure_upcross_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (T : ℝ≥0) {A : Set (LΩ S)} (hA : MeasurableSet[L𝓖 μ 0] A)
    {B : ℝ} (hB : ∀ ω ∈ A, tot (liftProj (ξ ω)) ≤ B) :
    LP μ (A ∩ {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧
      a ≤ F.Sp n s ω}) ≤ ENNReal.ofReal (ε / a) := by
  have hAm : MeasurableSet A := (L𝓖 μ).le 0 _ hA
  set Q := (LP μ).restrict A with hQ
  have : IsFiniteMeasure Q := by rw [hQ]; infer_instance
  have hτs := F.isStoppingTime_hitS hD0 hξ n ε
  obtain ⟨hiρ, eρ⟩ := F.integral_Sp_stop hD0 hξ n (F.isStoppingTime_hitUp hD0 hξ n ε a) T hA hB
  obtain ⟨hiτ, eτ⟩ := F.integral_Sp_stop hD0 hξ n hτs T hA hB
  rw [← hQ] at eρ eτ
  change Integrable _ Q at hiρ hiτ
  set A' : Set (LΩ S) := {ω | F.hitS n ε ω < T} with hA'def
  have hA' : MeasurableSet A' := (L𝓖 μ).le T _ (hτs.measurableSet_lt T)
  have hρτ : ∀ ω, F.hitS n ε ω ≤ F.hitUp n ε a ω := fun ω => by
    refine le_iInf₂ fun u hu => ?_
    by_contra hc
    have : F.postV n ε u ω = 0 := F.postV_of_lt n ε (not_le.1 hc)
    linarith
  have hc : ∀ ω ∈ A'ᶜ, F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω =
      F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω := fun ω hω => by
    have h1 : (T : WithTop ℝ≥0) ≤ F.hitS n ε ω := not_lt.1 hω
    rw [min_eq_left h1, min_eq_left (h1.trans (hρτ ω))]
  have hAeq : ∫ ω in A', F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω ∂Q =
      ∫ ω in A', F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω ∂Q := by
    have h1 := integral_add_compl hA' hiρ
    have h2 := integral_add_compl hA' hiτ
    rw [setIntegral_congr_fun hA'.compl hc] at h1
    linarith
  have hAle : ∫ ω in A', F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω ∂Q ≤ ε := by
    refine (setIntegral_mono_on (g := fun _ => ε) hiτ.integrableOn integrableOn_const hA'
      fun ω hω => ?_).trans ?_
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_lt (show F.hitS n ε ω < T from hω))
      rw [← hm, min_eq_right (hm ▸ (show F.hitS n ε ω < T from hω).le)]
      exact hitLe_attained (fun t => SolFamily.tendsto_nhdsGE_of_continuous
        (F.continuous_Sp n ω) t) hm.symm
    · rw [setIntegral_const, smul_eq_mul]
      have h1 : Q.real A' ≤ 1 := by
        rw [hQ, measureReal_restrict_apply hA']
        exact measureReal_le_one
      nlinarith [measureReal_nonneg (μ := Q) (s := A')]
  set f : LΩ S → ℝ :=
    A'.indicator fun ω => F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω
  have hf0 : 0 ≤ᵐ[Q] f := Eventually.of_forall fun ω => by
    simp only [f, Set.indicator]; split_ifs
    · exact (F.Sp_pos hξ n _ ω).le
    · exact le_rfl
  have hMk := mul_meas_ge_le_integral_of_nonneg hf0 (hiρ.indicator hA') a
  rw [integral_indicator hA', hAeq] at hMk
  have hsub : {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧ a ≤ F.Sp n s ω} ⊆
      {ω | a ≤ f ω} := by
    rintro ω ⟨hωA, s, hsT, hτs', has⟩
    have hV : F.postV n ε s ω ≤ -a := by rw [F.postV_of_le n ε hτs']; linarith
    have hρs : F.hitUp n ε a ω ≤ s := iInf₂_le s hV
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hρs)
    have hmT : (m : WithTop ℝ≥0) ≤ T := hm ▸ hρs.trans (WithTop.coe_le_coe.2 hsT)
    have hVm : F.postV n ε m ω ≤ -a :=
      hitLe_attained (fun t => F.postV_rightCont n ε ω t) hm.symm
    have hτm : F.hitS n ε ω ≤ m := by
      by_contra hc
      have : F.postV n ε m ω = 0 := F.postV_of_lt n ε (not_le.1 hc)
      linarith
    show a ≤ A'.indicator _ ω
    rw [Set.indicator_of_mem (show ω ∈ A' from hωA), ← hm, min_eq_right hmT]
    rw [F.postV_of_le n ε hτm] at hVm
    show a ≤ F.Sp n m ω
    linarith
  have hreal : Q.real {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧
      a ≤ F.Sp n s ω} ≤ ε / a := by
    rw [le_div_iff₀ ha]
    have := measureReal_mono (μ := Q) hsub (measure_ne_top _ _)
    nlinarith
  rw [Set.inter_comm, ← Measure.restrict_apply' hAm, ← hQ,
    ← ENNReal.ofReal_toReal (measure_ne_top Q _)]
  exact ENNReal.ofReal_le_ofReal hreal

end LiftFamily

end BlockBand.Transmission.DualLift
