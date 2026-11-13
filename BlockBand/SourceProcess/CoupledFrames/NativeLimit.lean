module

public import BlockBand.SourceProcess.Stochastic.SDE.NativeTools
public import BlockBand.SourceProcess.Stochastic.Integral.MultiplierStopped

/-!
# Limits of integrals

Measure `P = driverLaw μ` on the driver
space, `ν = timeProbMeasure T P` (`dt ⊗ P` on `(0,T]`) for integrands.

* `ae_eq_nativeIntegralOf_of_tendsto`: if integrands `g_n → g` in `L²(ν)` (every
  coordinate) and `I(g_n) = F_n` a.s. with `F_n → F` a.s., then `I(g) = F` a.s. (Itô isometry,
  convergence in measure and uniqueness of limits in measure).
* `tendsto_integral_sq_of_dominated`: dominated pointwise convergence gives `∫ (g_n − g)² → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- **Limits of integrals.** -/
theorem ae_eq_nativeIntegralOf_of_tendsto {g : ℕ → κ → ℝ × DriverSample S κ → ℝ}
    {g₀ : κ → ℝ × DriverSample S κ → ℝ} (hg : ∀ n, NativeIntegrand μ T (g n))
    (hg₀ : NativeIntegrand μ T g₀)
    (hint : ∀ c, Tendsto (fun n => ∫ p, (g n c p - g₀ c p) ^ 2
      ∂timeProbMeasure T (driverLaw (κ := κ) μ)) atTop (𝓝 0))
    {F : ℕ → DriverSample S κ → ℝ} {F₀ : DriverSample S κ → ℝ}
    (hF : ∀ n, (nativeIntegralOf (hg n) : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ] F n)
    (hlim : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => F n x) atTop (𝓝 (F₀ x))) :
    (nativeIntegralOf hg₀ : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ] F₀ := by
  have hL : Tendsto (fun n => nativeIntegralOf (hg n)) atTop (𝓝 (nativeIntegralOf hg₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have he (n : ℕ) : ‖nativeIntegralOf (hg n) - nativeIntegralOf hg₀‖ =
        Real.sqrt (∑ c, ∫ p, (g n c p - g₀ c p) ^ 2
          ∂timeProbMeasure T (driverLaw (κ := κ) μ)) := by
      rw [← nativeIntegralOf_sub, ← integral_sq_nativeIntegralOf, integral_sq_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg _)]
    simp_rw [he]
    have hs := tendsto_finsetSum (Finset.univ : Finset κ) fun c _ => hint c
    simp only [Finset.sum_const_zero] at hs
    have := (Real.continuous_sqrt.tendsto 0).comp hs
    rw [Real.sqrt_zero] at this
    exact this
  have hm1 := (tendstoInMeasure_of_tendsto_Lp hL).congr_left hF
  have hm2 := tendstoInMeasure_of_tendsto_ae
    (fun n => (Lp.aestronglyMeasurable (nativeIntegralOf (hg n))).congr (hF n)) hlim
  exact tendstoInMeasure_ae_unique hm1 hm2

omit [Fintype κ] [IsProbabilityMeasure μ] in
/-- Dominated convergence for the squared `L²` distance. -/
theorem tendsto_integral_sq_of_dominated {ν : Measure (ℝ × DriverSample S κ)}
    {g : ℕ → ℝ × DriverSample S κ → ℝ} {g₀ B : ℝ × DriverSample S κ → ℝ}
    (hg : ∀ n, AEStronglyMeasurable (g n) ν) (hg₀ : AEStronglyMeasurable g₀ ν)
    (hB : Integrable (fun p => (B p) ^ 2) ν) (hle : ∀ n p, |g n p - g₀ p| ≤ B p)
    (hlim : ∀ᵐ p ∂ν, Tendsto (fun n => g n p) atTop (𝓝 (g₀ p))) :
    Tendsto (fun n => ∫ p, (g n p - g₀ p) ^ 2 ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (F := fun n p => (g n p - g₀ p) ^ 2)
    (f := fun _ => 0) (fun p => (B p) ^ 2) (fun n => ((hg n).sub hg₀).pow 2) hB
    (fun n => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hle n p) 2)
    (hlim.mono fun p hp => by
      have ht := (hp.sub_const (g₀ p)).pow 2
      rw [sub_self, zero_pow two_ne_zero] at ht
      exact ht)
  simpa only [integral_zero] using h

end BlockBand.SourceProcess.CoupledFrames
