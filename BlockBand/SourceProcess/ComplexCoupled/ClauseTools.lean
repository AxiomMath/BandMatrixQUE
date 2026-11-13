module

public import BlockBand.SourceProcess.ComplexCoupled.BornG
public import BlockBand.SourceProcess.ModelExist.TransBound

/-!
# Tools for the stopped `𝒦` clauses

* `exists_bound_trace`: a continuous function of a frame is bounded on `Re tr(VᴴV) ≤ L`
  (compact Frobenius ball).
* `nativeIntegrand_of_frame`: if the diffusion of an Itô pair is a continuous function of a
  frame `X` whose squared norm is at most `L` before an augmented stopping time `ρ`, every stopped
  functional integrand is an integrand.
* `clause_fst`, `clause_mul`: the stopped (compensated product) martingale clauses at any random
  time `σ` a.s. equal to `ρ`, for any process `F` a.s. equal to the compensated one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [Fintype c]

theorem norm_sq_eq_re_trace (V : Matrix ι c ℂ) : ‖V‖ ^ 2 = ((Vᴴ * V).trace).re := by
  rw [← frob_sq_eq_trace, Complex.ofReal_re]

/-- **Continuous functions of a frame are bounded on trace balls.** -/
theorem exists_bound_trace {F : Type*} [NormedAddCommGroup F] {f : Matrix ι c ℂ → F}
    (hf : Continuous f) (L : ℝ) :
    ∃ C, ∀ V : Matrix ι c ℂ, ((Vᴴ * V).trace).re ≤ L → ‖f V‖ ≤ C := by
  have := FiniteDimensional.proper_real (Matrix ι c ℂ)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Matrix ι c ℂ)
    (Real.sqrt (max L 0))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, fun V hV => hC V ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [← norm_sq_eq_re_trace] at hV
  calc ‖V‖ = Real.sqrt (‖V‖ ^ 2) := (Real.sqrt_sq (norm_nonneg V)).symm
    _ ≤ Real.sqrt (max L 0) := Real.sqrt_le_sqrt (hV.trans (le_max_left _ _))

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Stopped integrands of a frame-driven pair.** -/
theorem nativeIntegrand_of_frame {Z : ℝ≥0 → DriverSample S κ → ℂ × ℂ}
    {φ : κ → ℝ≥0 → DriverSample S κ → ℂ × ℂ} (hZ : IsNativeItoProcess μ Z (fun _ _ => 0) φ)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    {X : ℝ≥0 → DriverSample S κ → Matrix ι c ℂ} {f : κ → Matrix ι c ℂ → ℂ × ℂ}
    (hf : ∀ a, Continuous (f a)) (hφ : ∀ a t x, φ a t x = f a (X t x)) {L : ℝ}
    (hL : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < ρ x →
      ((X s x)ᴴ * X s x).trace.re ≤ L) (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand ρ (functionalIntegrand ℓ φ)) := by
  choose C hC using fun a => exists_bound_trace (hf a) L
  refine nativeIntegrand_stop_bound hZ hρ ℓ (C := ‖ℓ‖ * ∑ a, |C a|) ?_ T
  filter_upwards [hL] with x hx s hs a
  rw [hφ, ← Real.norm_eq_abs]
  refine (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (hC a _ (hx s hs)).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun b => |C b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)))

/-- Linear images of driftless Itô processes are driftless. -/
theorem map_clm_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Y : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}
    (hY : IsNativeItoProcess μ Y (fun _ _ => 0) σ) (T : E →L[ℝ] F) :
    IsNativeItoProcess μ (fun t x => T (Y t x)) (fun _ _ => 0) (fun a t x => T (σ a t x)) := by
  have h := hY.map_clm T
  simp only [map_zero] at h
  exact h

variable {Z : ℝ≥0 → DriverSample S κ → ℂ × ℂ} {φ : κ → ℝ≥0 → DriverSample S κ → ℂ × ℂ}
  {ρ σ : DriverSample S κ → WithTop ℝ≥0} {F : ℝ≥0 → DriverSample S κ → ℂ}

/-- **Linear stopped clause.** -/
theorem clause_fst (hZ : IsNativeItoProcess μ Z (fun _ _ => 0) φ)
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    (hG : ∀ (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand ρ (functionalIntegrand ℓ φ)))
    (hρσ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ρ x = σ x)
    (hF : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, F t x = (Z t x).1 - (Z 0 x).1) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℂ, Martingale N (driverAugmented (κ := κ) μ)
      (driverLaw (κ := κ) μ) ∧ ∀ t, N t =ᵐ[driverLaw (κ := κ) μ] stoppedProcess F σ t := by
  obtain ⟨N, hN, hNe⟩ := exists_martingale_fst hZ hρ hG
  refine ⟨N, hN, fun t => ?_⟩
  filter_upwards [hNe t, hρσ, hF] with x h1 h2 h3
  rw [h1, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, h2, h3]

/-- **Compensated product stopped clause.** -/
theorem clause_mul (hZ : IsNativeItoProcess μ Z (fun _ _ => 0) φ)
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    (hG : ∀ (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand ρ (functionalIntegrand ℓ φ)))
    (hρσ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ρ x = σ x)
    (hF : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, F t x =
      ((Z t x).1 - (Z 0 x).1) * ((Z t x).2 - (Z 0 x).2) -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, (φ a s.toNNReal x).1 * (φ a s.toNNReal x).2) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℂ, Martingale N (driverAugmented (κ := κ) μ)
      (driverLaw (κ := κ) μ) ∧ ∀ t, N t =ᵐ[driverLaw (κ := κ) μ] stoppedProcess F σ t := by
  obtain ⟨N, hN, hNe⟩ := exists_martingale_mul hZ hρ hG
  refine ⟨N, hN, fun t => ?_⟩
  filter_upwards [hNe t, hρσ, hF] with x h1 h2 h3
  rw [h1, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, h2, h3]

end BlockBand.SourceProcess.ComplexCoupled
