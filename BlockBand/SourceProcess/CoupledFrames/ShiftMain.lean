module

public import BlockBand.SourceProcess.CoupledFrames.ShiftIto

/-!
# Increments after a stopping time

`isNativeItoProcess_shift`: for an Itô process `Y`, a stopping time `θ` and an
`𝓕_θ`-measurable weight `ξ`, the weighted increment process after `θ` (`shiftProc Y θ ξ`) is an
Itô process with coefficients `onAfter θ ξ b` and `onAfter θ ξ σ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.SourceProcess.Stochastic.ItoNative
open BlockBand.SourceProcess.Stochastic.Semimartingale

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y b : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}

omit [MeasurableSpace S] [Fintype κ] in
theorem stop_shiftLoc_eq (θ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ)
    (τ : ℕ → DriverSample S κ → WithTop ℝ≥0) (n : ℕ) (ρ : DriverSample S κ → WithTop ℝ≥0)
    (G : κ → ℝ × DriverSample S κ → ℝ) (c : κ) (p : ℝ × DriverSample S κ) :
    stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) G c p =
      if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ shiftLoc θ ξ τ n p.2 then
        stopIntegrand ρ G c p else 0 := by
  rw [← stopIntegrand_stopIntegrand]
  rfl

/-- **Increments after a stopping time, with an `𝓕_θ`-measurable weight, are Itô.** -/
theorem isNativeItoProcess_shift
    (hY : IsNativeItoProcess μ Y b σ) {θ : DriverSample S κ → WithTop ℝ≥0}
    (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ) {ξ : DriverSample S κ → ℝ}
    (hξ : StronglyMeasurable[hθ.measurableSpace] ξ) :
    IsNativeItoProcess μ (shiftProc Y θ ξ) (onAfter θ ξ b) (fun a => onAfter θ ξ (σ a)) := by
  obtain ⟨τ, hτs, hτl, hloc⟩ := hY.localizing
  refine ⟨stronglyMeasurable_shiftProc hY.progressive hθ hξ,
    isStronglyProgressive_shiftProc hY.progressive hθ hξ, ?_,
    isStronglyProgressive_onAfter hY.drift_progressive hθ hξ,
    fun a => isStronglyProgressive_onAfter (hY.diffusion_progressive a) hθ hξ, ?_,
    ⟨shiftLoc θ ξ τ, isStoppingTime_shiftLoc hθ hξ hτs, ae_tendsto_shiftLoc hτl, ?_⟩, ?_⟩
  · filter_upwards [hY.continuous] with x hx
    exact continuous_const.smul (hx.sub (hx.comp (continuous_stopTime (θ x))))
  · filter_upwards [hY.drift_integrable] with x hx t
    have e : (fun s : ℝ => onAfter θ ξ b s.toNNReal x) =
        {s : ℝ | θ x < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun s => ξ x • b s.toNNReal x) := by
      funext s; simp only [onAfter, indicator_apply, mem_ofPred_eq]
    rw [e]
    exact ((hx t).smul (ξ x)).indicator
      (measurableSet_lt measurable_const (WithTop.measurable_coe.comp measurable_real_toNNReal))
  · intro n ℓ T
    rw [functionalIntegrand_onAfter]
    have h := (nativeIntegrand_shift hθ hξ n (ρ := fun _ => ⊤)
      (nativeIntegrand_loc_min hloc hθ hξ isStoppingTime_top n ℓ T)).1
    convert h using 2
    funext x
    exact (min_eq_right le_top).symm
  · intro ℓ ρ hρ T hG t ht
    set G := fun a (p : ℝ × DriverSample S κ) => ξ p.2 * afterInt θ (functionalIntegrand ℓ σ) a p
    have hfi : functionalIntegrand ℓ (fun a => onAfter θ ξ (σ a)) = G :=
      functionalIntegrand_onAfter ℓ θ ξ σ
    have hF : NativeIntegrand μ T (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (functionalIntegrand ℓ (fun a => onAfter θ ξ (σ a)))) := by
      have h := stopIntegrand_nativeIntegrand hG (isStoppingTime_const _ t)
      rw [stopIntegrand_stopIntegrand] at h
      convert h using 2
      funext x
      exact min_comm _ _
    refine ⟨hF, ?_⟩
    choose hs he using fun n => shift_identity_loc hY hτs hloc hθ hξ ℓ hρ ht n
    refine (ae_eq_nativeIntegralOf_of_tendsto hs hF (fun c => ?_) (fun n => (he n).symm)
      ?_).symm
    · refine tendsto_integral_sq_of_dominated (B := fun p => |stopIntegrand
        (fun x => min (t : WithTop ℝ≥0) (ρ x)) (functionalIntegrand ℓ (fun a => onAfter θ ξ (σ a)))
          c p|) (fun n => (hs n c).1.mono (predictableSpace_le _))
        ((hF c).1.mono (predictableSpace_le _))
        ((hF c).2.integrable_sq.congr (ae_of_all _ fun p => (sq_abs _).symm)) (fun n p => ?_) ?_
      · rw [stop_shiftLoc_eq, hfi]
        split_ifs
        · simp only [G, sub_self, abs_zero]
          exact abs_nonneg _
        · simp
      · filter_upwards [ae_timeProb_of_ae (T := T) (ae_tendsto_shiftLoc (θ := θ) (ξ := ξ) hτl)]
          with p hp
        have hev := hp.eventually (lt_mem_nhds (WithTop.coe_lt_top p.1.toNNReal))
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [stop_shiftLoc_eq, hfi, ite_eq_left hn.le]
    · filter_upwards [ae_tendsto_shiftLoc (θ := θ) (ξ := ξ) hτl] with x hx
      have hev := hx.eventually (lt_mem_nhds (WithTop.coe_lt_top t))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hmin : min (t : WithTop ℝ≥0) (min (ρ x) (shiftLoc θ ξ τ n x)) =
          min (t : WithTop ℝ≥0) (ρ x) := by
        rw [← min_assoc]
        exact min_eq_left ((min_le_left _ _).trans hn.le)
      rw [stoppedProcess_congr_min _ (ρ := fun x => min (ρ x) (shiftLoc θ ξ τ n x)) (ρ' := ρ) hmin,
        stoppedDrift_congr_min (ρ := fun x => min (ρ x) (shiftLoc θ ξ τ n x)) (ρ' := ρ) hmin]

end BlockBand.SourceProcess.CoupledFrames
