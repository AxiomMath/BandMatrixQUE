module

public import BlockBand.SourceProcess.CoupledFrames.StopMultBdd
public import BlockBand.SourceProcess.CoupledFrames.ShiftMeas
public import BlockBand.SourceProcess.ModelExist.LocShift
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild

/-!
# Integrands after a stopping time and their localization

Measure `P = driverLaw μ`, augmented filtration, `ν = dt ⊗ P` on `(0,T]`.

* `afterInt θ g = 1{θ < s} g`; `functionalIntegrand_onAfter`: the functional integrand of the
  shifted diffusion `1{θ < s} ξ σ` is `ξ · afterInt θ (ℓ ∘ σ)`.
* `afterInt_stop`: `1{θ < s} g 1{s ≤ λ} = g 1{s ≤ λ} − g 1{s ≤ λ ∧ θ}`; hence
  `nativeIntegrand_afterInt` (both terms are integrands when `g 1{s ≤ λ}` is).
* `nativeIntegrand_shift`: with `λ_n = shiftLoc θ ξ τ n = τ_n ∧ truncStop n ξ θ` (`ModelExist.truncStop`:
  `⊤` where `|ξ| ≤ n`, `θ` elsewhere), the stopped shifted integrand is
  `truncW n ξ · afterInt θ (g 1{s ≤ τ_n})`, by `stopMult`.
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
open BlockBand.SourceProcess.ModelExist (truncW truncStop isStoppingTime_truncStop
  stronglyMeasurable_truncW norm_truncW_le)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

/-- `1{θ < s} g`. -/
def afterInt (θ : DriverSample S κ → WithTop ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ) :
    κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => if θ p.2 < ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) then g a p else 0

omit [MeasurableSpace S] [Fintype κ] in
theorem vanishBefore_afterInt (θ : DriverSample S κ → WithTop ℝ≥0)
    (g : κ → ℝ × DriverSample S κ → ℝ) : VanishBefore θ (afterInt θ g) := by
  intro a p hp
  simp only [afterInt, not_lt.2 hp, ↓reduceIte]

omit [MeasurableSpace S] [Fintype κ] in
theorem afterInt_stop (θ lam : DriverSample S κ → WithTop ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ) :
    afterInt θ (stopIntegrand lam g) = fun a p =>
      stopIntegrand lam g a p - stopIntegrand (fun x => min (lam x) (θ x)) g a p := by
  funext a p
  simp only [afterInt, stopIntegrand, le_min_iff]
  by_cases h1 : θ p.2 < ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0)
  · simp only [h1, ↓reduceIte, not_le.2 h1, and_false, sub_zero]
  · simp only [h1, ↓reduceIte, not_lt.1 h1, and_true]
    split_ifs <;> simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace S] [Fintype κ] in
theorem functionalIntegrand_onAfter (ℓ : E →L[ℝ] ℝ) (θ : DriverSample S κ → WithTop ℝ≥0)
    (ξ : DriverSample S κ → ℝ) (σ : κ → ℝ≥0 → DriverSample S κ → E) :
    functionalIntegrand ℓ (fun a => onAfter θ ξ (σ a)) =
      fun a p => ξ p.2 * afterInt θ (functionalIntegrand ℓ σ) a p := by
  funext a p
  simp only [functionalIntegrand, onAfter, afterInt]
  split_ifs
  · rw [map_smul, smul_eq_mul]
  · rw [map_zero, mul_zero]

omit [MeasurableSpace S] [Fintype κ] in
theorem stopIntegrand_mul (ρ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ)
    (h : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand ρ (fun a p => ξ p.2 * h a p) = fun a p => ξ p.2 * stopIntegrand ρ h a p := by
  funext a p
  simp only [stopIntegrand]
  split_ifs <;> simp

variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

theorem nativeIntegrand_afterInt {g : κ → ℝ × DriverSample S κ → ℝ}
    {θ lam : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    (hg : NativeIntegrand μ T (stopIntegrand lam g)) :
    NativeIntegrand μ T (afterInt θ (stopIntegrand lam g)) := by
  rw [afterInt_stop]
  refine nativeIntegrand_sub hg ?_
  have h2 := stopIntegrand_nativeIntegrand hg hθ
  rwa [stopIntegrand_stopIntegrand] at h2

/-- The localizer of the shifted process. -/
def shiftLoc (θ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ)
    (τ : ℕ → DriverSample S κ → WithTop ℝ≥0) (n : ℕ) : DriverSample S κ → WithTop ℝ≥0 :=
  fun x => min (τ n x) (truncStop n ξ θ x)

omit [MeasurableSpace S] [Fintype κ] in
theorem truncStop_le_of_gt {θ : DriverSample S κ → WithTop ℝ≥0} {ξ : DriverSample S κ → ℝ}
    {n : ℕ} {x : DriverSample S κ} (hx : ¬ |ξ x| ≤ n) : truncStop n ξ θ x = θ x := by
  simp only [truncStop, hx, ↓reduceIte]

omit [MeasurableSpace S] [Fintype κ] in
/-- The truncated weight agrees with the weight on the stopped shifted integrand. -/
theorem stop_afterInt_truncW (θ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ)
    (τ : ℕ → DriverSample S κ → WithTop ℝ≥0) (n : ℕ) (ρ : DriverSample S κ → WithTop ℝ≥0)
    (g : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) (fun a p => ξ p.2 * afterInt θ g a p) =
      fun a p => truncW n ξ p.2 * afterInt θ
        (stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) g) a p := by
  funext a p
  simp only [stopIntegrand, afterInt, truncW]
  by_cases hx : |ξ p.2| ≤ n
  · simp only [hx, ↓reduceIte]
    split_ifs <;> simp
  · simp only [hx, ↓reduceIte, zero_mul]
    have hs : ¬ (((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (ρ p.2) (shiftLoc θ ξ τ n p.2) ∧
        θ p.2 < ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0)) := by
      rintro ⟨h1, h2⟩
      have h3 : min (ρ p.2) (shiftLoc θ ξ τ n p.2) ≤ θ p.2 := by
        refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
        rw [truncStop_le_of_gt hx]
      exact absurd (h1.trans h3) (not_le.2 h2)
    by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (ρ p.2) (shiftLoc θ ξ τ n p.2)
    · by_cases h2 : θ p.2 < ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0)
      · exact absurd ⟨h1, h2⟩ hs
      · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1]

omit [IsProbabilityMeasure μ] in
theorem isStoppingTime_shiftLoc {θ : DriverSample S κ → WithTop ℝ≥0}
    (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ) {ξ : DriverSample S κ → ℝ}
    (hξ : StronglyMeasurable[hθ.measurableSpace] ξ) {τ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (τ n)) (n : ℕ) :
    IsStoppingTime (driverAugmented (κ := κ) μ) (shiftLoc θ ξ τ n) :=
  (hτ n).min (isStoppingTime_truncStop hθ hξ n)

omit [IsProbabilityMeasure μ] in
theorem ae_tendsto_shiftLoc {θ : DriverSample S κ → WithTop ℝ≥0} {ξ : DriverSample S κ → ℝ}
    {τ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    (hτl : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => τ n x) atTop (𝓝 ⊤)) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => shiftLoc θ ξ τ n x) atTop (𝓝 ⊤) :=
  hτl.mono fun x hx => Bridges.tendsto_min_top hx (ModelExist.tendsto_truncStop ξ θ x)

/-- **Integrands of the stopped shifted diffusion.** -/
theorem nativeIntegrand_shift {g : κ → ℝ × DriverSample S κ → ℝ}
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    {ξ : DriverSample S κ → ℝ} (hξ : StronglyMeasurable[hθ.measurableSpace] ξ)
    {τ : ℕ → DriverSample S κ → WithTop ℝ≥0} (n : ℕ) {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hg : NativeIntegrand μ T (stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x)) g)) :
    ∃ hs : NativeIntegrand μ T (stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x))
        (fun a p => ξ p.2 * afterInt θ g a p)),
      (nativeIntegralOf hs : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ] fun x =>
        truncW n ξ x * (nativeIntegralOf (nativeIntegrand_afterInt hθ hg) :
          DriverSample S κ → ℝ) x := by
  obtain ⟨hs0, he⟩ := stopMult (nativeIntegrand_afterInt hθ hg) hθ (vanishBefore_afterInt θ _)
    (stronglyMeasurable_truncW hθ hξ n) (C := n) (fun x => norm_truncW_le n ξ x)
  have hs : NativeIntegrand μ T (stopIntegrand (fun x => min (ρ x) (shiftLoc θ ξ τ n x))
      (fun a p => ξ p.2 * afterInt θ g a p)) := by
    rw [stop_afterInt_truncW]; exact hs0
  refine ⟨hs, ?_⟩
  have e : nativeIntegralOf hs = nativeIntegralOf hs0 :=
    nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => by
      rw [stop_afterInt_truncW]
  rw [e]
  exact he

end BlockBand.SourceProcess.CoupledFrames
