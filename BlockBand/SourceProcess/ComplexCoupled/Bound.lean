module

public import BlockBand.SourceProcess.ComplexCoupled.CPair
public import BlockBand.SourceProcess.CoupledFrames.NativeCongr

/-!
# Stopped integrands from a bound before the stop

`nativeIntegrand_stop_bound`: for an Itô process with diffusion `σ`, an augmented stopping
time `τ` and a functional `ℓ` with `|ℓ σ_a(s)| ≤ C` for `s < τ` (a.s.), the stopped integrand
`ℓ σ 1{s ≤ τ}` is an integrand on every horizon. Measurability: `ν`-a.e. limit of the
localized integrands `ℓ σ 1{s ≤ τ ∧ τ_n}`. The bound: `ν`-a.e. `s ≠ τ` (`ae_timeProb_ne`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A stopped integrand bounded before the stop is an integrand.** -/
theorem nativeIntegrand_stop_bound {X b : ℝ≥0 → DriverSample S κ → E}
    {σ : κ → ℝ≥0 → DriverSample S κ → E} (hX : IsNativeItoProcess μ X b σ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (ℓ : E →L[ℝ] ℝ) {C : ℝ}
    (hC : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < τ x → ∀ a,
      |ℓ (σ a s x)| ≤ C) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ σ)) := by
  obtain ⟨τn, -, hτl, hloc⟩ := hX.localizing
  have hn : ∀ n, NativeIntegrand μ T
      (stopIntegrand τ (stopIntegrand (τn n) (functionalIntegrand ℓ σ))) := fun n =>
    stopIntegrand_nativeIntegrand (hloc n ℓ T) hτ
  have hτm : Measurable τ := hτ.measurable.mono hτ.measurableSpace_le le_rfl
  intro a
  have hlim : ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ),
      Tendsto (fun n => stopIntegrand τ (stopIntegrand (τn n) (functionalIntegrand ℓ σ)) a p)
        atTop (𝓝 (stopIntegrand τ (functionalIntegrand ℓ σ) a p)) := by
    filter_upwards [ae_timeProb_of_ae (T := T) hτl] with p hp
    have hev : ∀ᶠ n in atTop, ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τn n p.2 :=
      (hp.eventually (lt_mem_nhds (WithTop.coe_lt_top _))).mono fun n hn => hn.le
    refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
    simp only [stopIntegrand, hn, ↓reduceIte]
  have hm := aestronglyMeasurable_sub_of_tendsto_ae (fun n => (hn n a).1) hlim
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (max C 0) ?_⟩
  filter_upwards [ae_timeProb_of_ae (T := T) hC,
    CoupledFrames.ae_timeProb_ne (θ := fun _ : Fin 1 => τ) (fun _ => hτm) T] with p hp hne
  simp only [stopIntegrand, functionalIntegrand, Real.norm_eq_abs]
  split_ifs with h
  · exact (hp _ (lt_of_le_of_ne h (hne 0)) a).trans (le_max_left _ _)
  · simp

end BlockBand.SourceProcess.ComplexCoupled
