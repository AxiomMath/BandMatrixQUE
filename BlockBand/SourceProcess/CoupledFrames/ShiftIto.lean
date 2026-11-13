module

public import BlockBand.SourceProcess.CoupledFrames.ShiftDrift

/-!
# **Increments after a stopping time with an `𝓕_θ`-measurable weight are Itô**

`isNativeItoProcess_shift`: if `Y` is an Itô process with drift `b` and diffusion `σ`, `θ`
an augmented stopping time and `ξ` an `𝓕_θ`-measurable real weight (no bound), then
`ξ (Y − Y^θ)` is an Itô process with drift `1{θ < s} ξ b` and diffusion `1{θ < s} ξ σ`.

Localization: `λ_n = τ_n ∧ truncStop n ξ θ` (`τ_n` localizes `Y`). Identity clause: for a stopping
time `ρ` and `λ = ρ ∧ λ_n`, the identities of `Y` at `λ` and `λ ∧ θ` give
`(ℓ(Y − Y^θ) − drift)_{t∧λ} = I(1{θ < s} ℓσ 1{s ≤ t∧λ})`; multiplying by the bounded
`truncW n ξ` (`stopMult`) gives the stopped identity of the shifted process at `t ∧ λ`
(`shift_identity_loc`); then `n → ∞` (`ae_eq_nativeIntegralOf_of_tendsto`; both sides are
eventually constant in `n`, resp. dominated by the target integrand).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.SourceProcess.Stochastic.ItoNative
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.ModelExist (truncW truncStop isStoppingTime_truncStop)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y b : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}

/-- Integrands of `Y` stopped at `ρ ∧ λ_n`. -/
theorem nativeIntegrand_loc_min {τ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    (hloc : ∀ n (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0), NativeIntegrand μ T
      (stopIntegrand (τ n) (functionalIntegrand ℓ σ)))
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    {ξ : DriverSample S κ → ℝ} (hξ : StronglyMeasurable[hθ.measurableSpace] ξ)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    (n : ℕ) (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x))
      (functionalIntegrand ℓ σ)) := by
  have h := stopIntegrand_nativeIntegrand (hloc n ℓ T) (hρ.min (isStoppingTime_truncStop hθ hξ n))
  rw [stopIntegrand_stopIntegrand] at h
  convert h using 2
  funext x
  simp only [shiftLoc]
  exact min_left_comm _ _ _

omit [MeasurableSpace S] [Fintype κ] in
theorem shiftLoc_le_theta {θ : DriverSample S κ → WithTop ℝ≥0} {ξ : DriverSample S κ → ℝ}
    {τ : ℕ → DriverSample S κ → WithTop ℝ≥0} {n : ℕ} {x : DriverSample S κ}
    (hx : ¬ |ξ x| ≤ n) : shiftLoc θ ξ τ n x ≤ θ x :=
  (min_le_right _ _).trans (truncStop_le_of_gt hx).le

/-- **The localized identity of the shifted process.** -/
theorem shift_identity_loc (hY : IsNativeItoProcess μ Y b σ)
    {τ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    (hτs : ∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (τ n))
    (hloc : ∀ n (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0), NativeIntegrand μ T
      (stopIntegrand (τ n) (functionalIntegrand ℓ σ)))
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    {ξ : DriverSample S κ → ℝ} (hξ : StronglyMeasurable[hθ.measurableSpace] ξ)
    (ℓ : E →L[ℝ] ℝ) {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ) {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) :
    ∃ hs : NativeIntegrand μ T (stopIntegrand
        (fun x => min (min (t : WithTop ℝ≥0) (ρ x)) (shiftLoc θ ξ τ n x))
        (fun a p => ξ p.2 * afterInt θ (functionalIntegrand ℓ σ) a p)),
      (fun x => ℓ (stoppedProcess (shiftProc Y θ ξ) (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) t x) -
          ℓ (shiftProc Y θ ξ 0 x) -
          ℓ (stoppedDrift (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) (onAfter θ ξ b) t x))
        =ᵐ[driverLaw (κ := κ) μ] (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  set lam : DriverSample S κ → WithTop ℝ≥0 := fun x => min (ρ x) (shiftLoc θ ξ τ n x) with hlamdef
  have hlam : IsStoppingTime (driverAugmented (κ := κ) μ) lam :=
    hρ.min (isStoppingTime_shiftLoc hθ hξ hτs n)
  have hN1 := nativeIntegrand_loc_min hloc hθ hξ hρ n ℓ T
  obtain ⟨hs1, e1⟩ := hY.identity ℓ lam hlam T hN1 t ht
  have hN2 : NativeIntegrand μ T (stopIntegrand (fun x => min (lam x) (θ x))
      (functionalIntegrand ℓ σ)) := by
    have := stopIntegrand_nativeIntegrand hN1 hθ
    rwa [stopIntegrand_stopIntegrand] at this
  obtain ⟨hs2, e2⟩ := hY.identity ℓ (fun x => min (lam x) (θ x)) (hlam.min hθ) T hN2 t ht
  have hm1 : (fun x => min (min (t : WithTop ℝ≥0) (ρ x)) (shiftLoc θ ξ τ n x)) =
      fun x => min (t : WithTop ℝ≥0) (lam x) := funext fun x => min_assoc _ _ _
  have hg : NativeIntegrand μ T (stopIntegrand
      (fun x => min (min (t : WithTop ℝ≥0) (ρ x)) (shiftLoc θ ξ τ n x)) (functionalIntegrand ℓ σ)) :=
    by rw [hm1]; exact hs1
  obtain ⟨hs, he⟩ := nativeIntegrand_shift hθ hξ n hg
  refine ⟨hs, ?_⟩
  have hI : nativeIntegralOf (nativeIntegrand_afterInt hθ hg) =
      nativeIntegralOf hs1 - nativeIntegralOf hs2 := by
    rw [← nativeIntegralOf_sub]
    refine nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => ?_
    rw [afterInt_stop, hm1]
    simp only [hlamdef, min_assoc]
  filter_upwards [he, e1, e2, hI ▸ Lp.coeFn_sub (nativeIntegralOf hs1) (nativeIntegralOf hs2),
    hY.drift_integrable] with x hx hx1 hx2 hx3 hb
  rw [hx, hx3, Pi.sub_apply, ← hx1, ← hx2, stoppedProcess_shiftProc, shiftProc_zero,
    stoppedDrift_onAfter (hb t), map_smul, map_smul, map_sub, map_sub, map_zero, smul_eq_mul,
    smul_eq_mul]
  by_cases hxn : |ξ x| ≤ n
  · simp only [truncW, hxn, ↓reduceIte]
    ring
  · have hle : lam x ≤ θ x := (min_le_right _ _).trans (shiftLoc_le_theta hxn)
    have hmin : min (t : WithTop ℝ≥0) (min (lam x) (θ x)) = min (t : WithTop ℝ≥0) (lam x) := by
      rw [min_eq_left hle]
    rw [stoppedProcess_congr_min Y (ρ := fun x => min (lam x) (θ x)) (ρ' := lam) hmin,
      stoppedDrift_congr_min (ρ := fun x => min (lam x) (θ x)) (ρ' := lam) hmin]
    simp only [truncW, hxn, ↓reduceIte]
    ring

end BlockBand.SourceProcess.CoupledFrames
