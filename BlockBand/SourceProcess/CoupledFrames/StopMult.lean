module

public import BlockBand.SourceProcess.CoupledFrames.NativeLimit
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableRaw

/-!
# `𝓕_θ`-measurable multipliers after a stopping time

Measure `P = driverLaw μ`, augmented filtration `𝓖 = driverAugmented μ`, integrands on `(0,T]` for
`ν = dt ⊗ P`.

Let `θ` be an augmented stopping time and `g` an integrand vanishing on `{s ≤ θ}`
(`VanishBefore`). For a bounded `𝓕_θ`-measurable `H`, `H g` is an integrand and
`I(H g) = H I(g)` a.s. (`stopMult`).

Proof: for `A ∈ 𝓕_θ` the time `θ_A = θ` on `A`, `⊤` off `A`, is a stopping time and
`1_A g = g − g 1{s ≤ θ_A}`, so `I(1_A g) = X_T − X_{T ∧ θ_A}` (`nativeAdaptedLimit_stopped`)
`= 1_A X_T`, because `X_{T∧θ} = I(g 1{s ≤ T∧θ}) = 0` (`indicator_mult`). Simple functions follow
by linearity, bounded ones by approximation, the isometry and
`ae_eq_nativeIntegralOf_of_tendsto`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- `g` vanishes on the stochastic interval `{s ≤ θ}`. -/
def VanishBefore (θ : DriverSample S κ → WithTop ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ) : Prop :=
  ∀ c p, ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ θ p.2 → g c p = 0

/-- `θ` on `A`, `⊤` off `A`. -/
def stopOn (A : Set (DriverSample S κ)) [DecidablePred (· ∈ A)]
    (θ : DriverSample S κ → WithTop ℝ≥0) : DriverSample S κ → WithTop ℝ≥0 :=
  fun x => if x ∈ A then θ x else ⊤

omit [IsProbabilityMeasure μ] in
theorem isStoppingTime_stopOn {θ : DriverSample S κ → WithTop ℝ≥0}
    (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ) {A : Set (DriverSample S κ)}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet[hθ.measurableSpace] A) :
    IsStoppingTime (driverAugmented (κ := κ) μ) (stopOn A θ) := by
  intro t
  have e : {x | stopOn A θ x ≤ t} = A ∩ {x | θ x ≤ t} := by
    ext x
    by_cases hx : x ∈ A
    · simp [stopOn, hx]
    · simp only [stopOn, hx, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, false_and, iff_false]
      exact WithTop.not_top_le_coe t
  rw [e]
  exact ((hθ.measurableSet A).1 hA).2 t

omit [MeasurableSpace S] [Fintype κ] [IsProbabilityMeasure μ] in
theorem stoppedProcess_top' (X : ℝ≥0 → DriverSample S κ → ℝ) (u : ℝ≥0) :
    stoppedProcess X (fun _ => ⊤) u = X u := by
  funext x
  exact stoppedProcess_eq_of_le le_top

theorem nativeIntegrand_min_horizon {g : κ → ℝ × DriverSample S κ → ℝ}
    (τ : DriverSample S κ → WithTop ℝ≥0) (c : κ) :
    stopIntegrand (fun x => min (T : WithTop ℝ≥0) (τ x)) g c
      =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] stopIntegrand τ g c := by
  filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
  have hT : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) := by
    rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    exact hp.2
  simp only [stopIntegrand, le_min_iff, hT, true_and]

/-- The terminal integral is the draft process at the horizon. -/
theorem nativeIntegralOf_eq_limit {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) :
    (nativeIntegralOf hg : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      nativeAdaptedLimit μ T hg.family T := by
  have htop : IsStoppingTime (driverAugmented (κ := κ) μ)
      (fun _ : DriverSample S κ => (⊤ : WithTop ℝ≥0)) := isStoppingTime_top
  obtain ⟨hs, h⟩ := nativeAdaptedLimit_stopped hg htop T
  rw [stoppedProcess_top'] at h
  have he : nativeIntegralOf hs = nativeIntegralOf hg :=
    nativeIntegralOf_congr hs hg fun c => (nativeIntegrand_min_horizon _ c).trans
      (Eventually.of_forall fun p => ite_eq_left le_top)
  rw [he] at h
  exact h.symm

/-- **Indicator multipliers.** -/
theorem indicator_mult {g : κ → ℝ × DriverSample S κ → ℝ} (hg : NativeIntegrand μ T g)
    {θ : DriverSample S κ → WithTop ℝ≥0} (hθ : IsStoppingTime (driverAugmented (κ := κ) μ) θ)
    (hv : VanishBefore θ g) {A : Set (DriverSample S κ)} (hA : MeasurableSet[hθ.measurableSpace] A) :
    ∃ hs : NativeIntegrand μ T (fun c p => A.indicator (fun _ => (1 : ℝ)) p.2 * g c p),
      (nativeIntegralOf hs : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
        fun x => A.indicator (fun _ => (1 : ℝ)) x * (nativeIntegralOf hg : DriverSample S κ → ℝ) x := by
  classical
  have hA' : IsStoppingTime (driverAugmented (κ := κ) μ) (stopOn A θ) :=
    isStoppingTime_stopOn hθ hA
  have hs1 := stopIntegrand_nativeIntegrand hg hA'
  have hpt : (fun c p => A.indicator (fun _ => (1 : ℝ)) p.2 * g c p) =
      fun c p => g c p - stopIntegrand (stopOn A θ) g c p := by
    funext c p
    by_cases hx : p.2 ∈ A
    · simp only [indicator_of_mem hx, one_mul, stopIntegrand, stopOn, hx, ↓reduceIte]
      split_ifs with h
      · rw [hv c p h, sub_zero]
      · rw [sub_zero]
    · simp only [indicator_of_notMem hx, zero_mul, stopIntegrand, stopOn, hx, ↓reduceIte, le_top,
        sub_self]
  have hs : NativeIntegrand μ T (fun c p => A.indicator (fun _ => (1 : ℝ)) p.2 * g c p) := by
    rw [hpt]; exact nativeIntegrand_sub hg hs1
  refine ⟨hs, ?_⟩
  have hI : nativeIntegralOf hs = nativeIntegralOf hg - nativeIntegralOf hs1 := by
    rw [← nativeIntegralOf_sub]
    exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p =>
      congrFun (congrFun hpt c) p
  obtain ⟨hs2, h2⟩ := nativeAdaptedLimit_stopped hg hA' T
  have he2 : nativeIntegralOf hs2 = nativeIntegralOf hs1 :=
    nativeIntegralOf_congr hs2 hs1 fun c => nativeIntegrand_min_horizon _ c
  rw [he2] at h2
  obtain ⟨hs3, h3⟩ := nativeAdaptedLimit_stopped hg hθ T
  have he3 : nativeIntegralOf hs3 = nativeIntegralOf (nativeIntegrand_zero (μ := μ) (T := T)) :=
    nativeIntegralOf_congr hs3 _ fun c => Eventually.of_forall fun p => by
      simp only [stopIntegrand]
      split_ifs with h
      · exact hv c p (h.trans (min_le_right _ _))
      · rfl
  rw [he3, nativeIntegralOf_zero] at h3
  filter_upwards [hI ▸ Lp.coeFn_sub (nativeIntegralOf hg) (nativeIntegralOf hs1), h2, h3,
    nativeIntegralOf_eq_limit hg, Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)] with x h1 hx2 hx3 hx4 hx0
  rw [h1, Pi.sub_apply, ← hx2, hx4]
  by_cases hx : x ∈ A
  · have e : stoppedProcess (nativeAdaptedLimit μ T hg.family) (stopOn A θ) T x =
        stoppedProcess (nativeAdaptedLimit μ T hg.family) θ T x := by
      simp only [stoppedProcess, stopOn, hx, ↓reduceIte]
    rw [e, hx3, hx0, indicator_of_mem hx]
    simp
  · have e : stoppedProcess (nativeAdaptedLimit μ T hg.family) (stopOn A θ) T x =
        nativeAdaptedLimit μ T hg.family T x := by
      have e' : stoppedProcess (nativeAdaptedLimit μ T hg.family) (stopOn A θ) T x =
          stoppedProcess (nativeAdaptedLimit μ T hg.family) (fun _ => ⊤) T x := by
        simp only [stoppedProcess, stopOn, hx, ↓reduceIte]
      rw [e', stoppedProcess_top']
    rw [e, indicator_of_notMem hx]
    simp

end BlockBand.SourceProcess.CoupledFrames
