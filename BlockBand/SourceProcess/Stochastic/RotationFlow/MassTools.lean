module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Unique
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Tools for the second-moment equations

* `integral_nativeIntegralOf_eq_zero`: the integral has mean zero under `driverLaw μ`
  (it is the terminal value of the continuous stopped-integral martingale, which starts at `0`).
* `nativeIntegrand_coeffF_ae`: an `F`-valued version of `nativeIntegrand_coeff_ae`.
* `continuousOn_massGenerator`, `exists_massGenerator_bound`: the mass generator is continuous on
  `[a,c]` and its entries are uniformly bounded there.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.Internal.Contracts.TransmissionFlow

variable {S κ' : Type*} [MeasurableSpace S] [Fintype κ'] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Mean zero** of the integral. -/
theorem integral_nativeIntegralOf_eq_zero {T : ℝ≥0} {g : κ' → ℝ × DriverSample S κ' → ℝ}
    (hg : NativeIntegrand μ T g) :
    ∫ x, (nativeIntegralOf hg : DriverSample S κ' → ℝ) x ∂driverLaw (κ := κ') μ = 0 := by
  have h1 := nativeAdaptedLimit_terminal_ae μ T hg.family
  have h2 := (nativeAdaptedLimit_martingale μ T hg.family).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T)
    (s := univ) MeasurableSet.univ
  rw [setIntegral_univ, setIntegral_univ, nativeAdaptedLimit_initial] at h2
  unfold nativeIntegralOf
  rw [← integral_congr_ae h1, ← h2]
  simp

/-- Stopped `F`-valued coefficient functionals bounded along a.s. continuous adapted paths are
integrands. -/
theorem nativeIntegrand_coeffF_ae {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {σ : κ' → ℝ≥0 → E → F} (hσ : ∀ a, Continuous fun q : ℝ≥0 × E => σ a q.1 q.2)
    {X : ℝ≥0 → DriverSample S κ' → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ') μ t] (X t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ') μ, Continuous fun t => X t x) {C : ℝ}
    (hC : ∀ᵐ x ∂driverLaw (κ := κ') μ, ∀ a t, ‖σ a t (X t x)‖ ≤ C)
    (ℓ : F →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand (fun _ => ⊤)
      (functionalIntegrand ℓ fun a t x => σ a t (X t x))) := by
  intro a
  have hm : AEStronglyMeasurable[rawPredictable S κ']
      (fun p : ℝ × DriverSample S κ' => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)))
      (timeProbMeasure T (driverLaw (κ := κ') μ)) :=
    ℓ.continuous.comp_aestronglyMeasurable
      ((hσ a).comp_aestronglyMeasurable (aesm_clock.prodMk (aesm_processFun hXa hXc)))
  have he : stopIntegrand (fun _ => ⊤) (functionalIntegrand ℓ fun a t x => σ a t (X t x)) a =
      fun p : ℝ × DriverSample S κ' => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)) := by
    funext p
    simp only [stopIntegrand, le_top, ite_true, functionalIntegrand]
  rw [he]
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (‖ℓ‖ * C) ?_⟩
  filter_upwards [ae_timeProb_of_ae (T := T) hC] with p hp
  exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hp a _) (norm_nonneg _))

variable {N : ℕ} {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}

theorem continuousOn_massGenerator (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) :
    ContinuousOn (fun y => massGenerator r κ y) (Set.Icc a c) := by
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  have hr' : ∀ k m : Fin N, ContinuousOn (fun y => r y k m) (Set.Icc a c) := fun k m =>
    (continuous_apply m).comp_continuousOn ((continuous_apply k).comp_continuousOn hrc)
  have hκ' : ContinuousOn (fun y => κ y k) (Set.Icc a c) :=
    (continuous_apply k).comp_continuousOn hκc
  unfold massGenerator
  by_cases hkl : k = l
  · simp only [hkl, ite_true]
    subst hkl
    exact ((continuousOn_finsetSum _ fun m _ => hr' k m).neg).sub hκ'
  · simp only [hkl, ite_false]
    exact hr' k l

theorem exists_massGenerator_bound (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc a c, ∀ k l, |massGenerator r κ y k l| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn
    (continuousOn_massGenerator hrc hκc)
  refine ⟨max K 0, le_max_right _ _, fun y hy k l => ?_⟩
  have h1 : ‖massGenerator r κ y k‖ ≤ ‖massGenerator r κ y‖ := norm_le_pi_norm _ k
  have h2 : ‖massGenerator r κ y k l‖ ≤ ‖massGenerator r κ y k‖ := norm_le_pi_norm _ l
  rw [← Real.norm_eq_abs]
  exact h2.trans (h1.trans ((hK y hy).trans (le_max_left _ _)))

end BlockBand.SourceProcess.Stochastic.RotationFlow
