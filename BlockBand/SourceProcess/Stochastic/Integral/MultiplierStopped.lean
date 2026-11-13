module
public import BlockBand.SourceProcess.Stochastic.Integral.Main
public import BlockBand.SourceProcess.Stochastic.Integral.Multiplier
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopped integrands as integrands, and indistinguishability

Measure `driverLaw μ`, raw filtration `F`, augmented stopping times (`F_t ∨ N`), integrands in
`L²(dt ⊗ driverLaw μ)` on `(0,T]`; `X^g = nativeAdaptedLimit μ T hg.family`.

* `nativeAdaptedLimit_stopped`: the stopped identity of `ContinuousStoppedIntegral` for the
  concrete process `X^g`
  (`X^g_{u ∧ τ} = I_T(g 1{s ≤ u ∧ τ})`); `continuousStoppedIntegral_holds` only exposes `∃ X`.
* `stopIntegrand_nativeIntegrand`: `g 1{s ≤ τ}` is an integrand.
* `nativeAdaptedLimit_stopIntegrand`: **timewise stopped identity**
  `X^{g 1{s ≤ τ}}_v = X^g_{v ∧ τ}` a.s., for every `v` and augmented stopping time `τ`.
* `indistinguishable_of_continuous`: two a.s. continuous processes that agree a.s. at each time
  agree a.s. at all times simultaneously; `ae_eq_nativeAdaptedLimit_of_stopped` and
  `indistinguishable_nativeAdaptedLimit` transfer these identities to any continuous version.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion

section Indistinguishable
variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [TopologicalSpace E] [T2Space E]

/-- Two a.s. continuous processes that are a.s. equal at every fixed time are indistinguishable. -/
theorem indistinguishable_of_continuous {X Y : ℝ≥0 → Ω → E}
    (hX : ∀ᵐ x ∂P, Continuous fun t => X t x) (hY : ∀ᵐ x ∂P, Continuous fun t => Y t x)
    (h : ∀ t, X t =ᵐ[P] Y t) : ∀ᵐ x ∂P, ∀ t, X t x = Y t x := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ x ∂P, ∀ t : D, X t x = Y t x := ae_all_iff.2 fun t => h t
  filter_upwards [hX, hY, hall] with x hx hy hxy
  intro t
  have he := Continuous.ext_on hD hx hy (fun s hs => hxy ⟨s, hs⟩)
  exact congrFun he t

omit [TopologicalSpace E] [T2Space E] in
theorem stoppedProcess_ae_eq_of_indistinguishable {X Y : ℝ≥0 → Ω → E}
    (h : ∀ᵐ x ∂P, ∀ t, X t x = Y t x) (τ : Ω → WithTop ℝ≥0) (u : ℝ≥0) :
    stoppedProcess X τ u =ᵐ[P] stoppedProcess Y τ u := by
  filter_upwards [h] with x hx
  exact hx _

end Indistinguishable

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- **The stopped-integral identities for the concrete process**
`X^g = nativeAdaptedLimit μ T hg.family`. -/
theorem nativeAdaptedLimit_stopped {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) (u : ℝ≥0) :
    ∃ hs : NativeIntegrand μ T (stopIntegrand (fun x => min (u : WithTop ℝ≥0) (τ x)) g),
      stoppedProcess (nativeAdaptedLimit μ T hg.family) τ u =ᵐ[driverLaw (κ := κ) μ]
        (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  classical
  have hne (x : DriverSample S κ) : min (u : WithTop ℝ≥0) (τ x) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  let σ : DriverSample S κ → ℝ≥0 := fun x => (min (u : WithTop ℝ≥0) (τ x)).untop (hne x)
  have hσcoe (x : DriverSample S κ) : (σ x : WithTop ℝ≥0) = min (u : WithTop ℝ≥0) (τ x) :=
    WithTop.coe_untop _ _
  have hσu (x : DriverSample S κ) : σ x ≤ u := by
    have h := min_le_left (u : WithTop ℝ≥0) (τ x)
    rw [← hσcoe x] at h
    exact_mod_cast h
  have hσ (t : ℝ≥0) : MeasurableSet[driverAugmented (κ := κ) μ t] {x | σ x ≤ t} := by
    have he : {x | σ x ≤ t} = {ω | min (τ ω) (u : WithTop ℝ≥0) ≤ t} := by
      ext x
      change σ x ≤ t ↔ min (τ x) (u : WithTop ℝ≥0) ≤ t
      rw [min_comm, ← hσcoe x, WithTop.coe_le_coe]
    rw [he]
    exact hτ.min_const u t
  have hst : stopIntegrand (fun x => min (u : WithTop ℝ≥0) (τ x)) g = stopFn σ g := by
    rw [← stopIntegrand_coe]
    congr 1
    funext x
    exact (hσcoe x).symm
  rw [hst]
  obtain ⟨hs, hae⟩ := stopped_identity_of_bounded hg hσu hσ
  refine ⟨hs, ?_⟩
  have hsp : stoppedProcess (nativeAdaptedLimit μ T hg.family) τ u =
      fun x => nativeAdaptedLimit μ T hg.family (σ x) x := by
    funext x
    simp only [stoppedProcess]
    rw [WithTop.untopA_eq_untop (hne x)]
  rw [hsp]
  exact hae

omit [MeasurableSpace S] [Fintype κ] in
theorem stopIntegrand_min_stopIntegrand (τ : DriverSample S κ → WithTop ℝ≥0) (v : ℝ≥0)
    (g : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand (fun _ => (v : WithTop ℝ≥0)) (stopIntegrand τ g) =
      stopIntegrand (fun x => min (v : WithTop ℝ≥0) (τ x)) g := by
  funext c p
  simp only [stopIntegrand, le_min_iff]
  split_ifs <;> simp_all

/-- `g · 1{s ≤ τ}` is an integrand for every augmented stopping time `τ`. -/
theorem stopIntegrand_nativeIntegrand {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) :
    NativeIntegrand μ T (stopIntegrand τ g) := by
  obtain ⟨hs, -⟩ := nativeAdaptedLimit_stopped hg hτ T
  refine NativeIntegrand.congr hs fun c => ?_
  filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
  have hT : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) := by
    rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    exact hp.2
  simp only [stopIntegrand, le_min_iff, hT, true_and]

/-- **Timewise stopped identity.** For every augmented stopping time `τ` and time `v`,
`X^{g 1{s ≤ τ}}_v = X^g_{v ∧ τ}` almost surely. -/
theorem nativeAdaptedLimit_stopIntegrand {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (hgτ : NativeIntegrand μ T (stopIntegrand τ g)) (v : ℝ≥0) :
    nativeAdaptedLimit μ T hgτ.family v =ᵐ[driverLaw (κ := κ) μ]
      stoppedProcess (nativeAdaptedLimit μ T hg.family) τ v := by
  obtain ⟨hs1, h1⟩ := nativeAdaptedLimit_stopped hgτ
    (isStoppingTime_const (driverAugmented (κ := κ) μ) v) v
  obtain ⟨hs2, h2⟩ := nativeAdaptedLimit_stopped hg hτ v
  have hc : (fun _ : DriverSample S κ => min (v : WithTop ℝ≥0) (v : WithTop ℝ≥0)) =
      fun _ => (v : WithTop ℝ≥0) := funext fun _ => min_self _
  have he : nativeIntegralOf hs1 = nativeIntegralOf hs2 := by
    apply nativeIntegralOf_congr
    intro c
    refine Eventually.of_forall fun p => ?_
    rw [hc, stopIntegrand_min_stopIntegrand]
  have hconst : stoppedProcess (nativeAdaptedLimit μ T hgτ.family)
      (fun _ => (v : WithTop ℝ≥0)) v = nativeAdaptedLimit μ T hgτ.family v := by
    funext x
    exact stoppedProcess_eq_of_le le_rfl
  rw [hconst] at h1
  rw [he] at h1
  exact h1.trans h2.symm

/-- Any process satisfying the deterministic-time stopped-integral identities for `g` is a
version of
`X^g`. -/
theorem ae_eq_nativeAdaptedLimit_of_stopped {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {X : ℝ≥0 → DriverSample S κ → ℝ}
    (hX : ∀ u : ℝ≥0, ∃ hs : NativeIntegrand μ T
      (stopIntegrand (fun _ => min (u : WithTop ℝ≥0) ⊤) g),
      stoppedProcess X (fun _ => ⊤) u =ᵐ[driverLaw (κ := κ) μ]
        (nativeIntegralOf hs : DriverSample S κ → ℝ)) (u : ℝ≥0) :
    X u =ᵐ[driverLaw (κ := κ) μ] nativeAdaptedLimit μ T hg.family u := by
  obtain ⟨hs, h⟩ := hX u
  have htopst : IsStoppingTime (driverAugmented (κ := κ) μ)
      (fun _ : DriverSample S κ => (⊤ : WithTop ℝ≥0)) := fun i => by
    simp only [top_le_iff, WithTop.coe_ne_top, Set.ofPred_false]
    exact @MeasurableSet.empty _ (driverAugmented (κ := κ) μ i)
  obtain ⟨hs', h'⟩ := nativeAdaptedLimit_stopped hg htopst u
  have htop (Y : ℝ≥0 → DriverSample S κ → ℝ) : stoppedProcess Y (fun _ => ⊤) u = Y u := by
    funext x
    exact stoppedProcess_eq_of_le le_top
  rw [htop] at h h'
  rw [nativeIntegralOf_congr hs hs' (fun _ => EventuallyEq.rfl)] at h
  exact h.trans h'.symm

/-- Any a.s. continuous process satisfying the deterministic-time stopped-integral identities is
indistinguishable from `X^g`; in particular all stopped identities transfer to it
(`stoppedProcess_ae_eq_of_indistinguishable`). -/
theorem indistinguishable_nativeAdaptedLimit {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {X : ℝ≥0 → DriverSample S κ → ℝ}
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x)
    (hX : ∀ u : ℝ≥0, ∃ hs : NativeIntegrand μ T
      (stopIntegrand (fun _ => min (u : WithTop ℝ≥0) ⊤) g),
      stoppedProcess X (fun _ => ⊤) u =ᵐ[driverLaw (κ := κ) μ]
        (nativeIntegralOf hs : DriverSample S κ → ℝ)) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = nativeAdaptedLimit μ T hg.family t x :=
  indistinguishable_of_continuous hXc (nativeAdaptedLimit_continuous_all_ae μ T hg.family)
    (ae_eq_nativeAdaptedLimit_of_stopped hg hX)

end BlockBand.SourceProcess.Stochastic.Integral
