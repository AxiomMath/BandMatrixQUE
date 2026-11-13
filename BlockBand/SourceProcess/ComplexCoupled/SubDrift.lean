module

public import BlockBand.SourceProcess.ComplexCoupled.Bound
public import BlockBand.SourceProcess.ModelExist.GramLoc

/-!
# Subtracting the drift integral of a complex Itô process

`isNativeItoProcess_sub_drift`: if `F` is a complex Itô process with drift `b` and diffusion
`φ`, then its compensated process `F_t - F_0 - ∫_0^t b` is an Itô process with zero drift
and the same diffusion. Used for the compensated Gram coordinates (`gramCompensated`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Integral

/-- Primitives of locally integrable complex paths are continuous. -/
theorem continuous_setIntegral_Ioc_C' {g : ℝ≥0 → ℂ}
    (hg : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc 0 t)) :
    Continuous fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, g s.toNNReal := by
  have h1 := continuous_setIntegral_Ioc (g := fun u => (g u).re) fun t => (hg t).re
  have h2 := continuous_setIntegral_Ioc (g := fun u => (g u).im) fun t => (hg t).im
  have e : (fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, g s.toNNReal) = fun u : ℝ≥0 =>
      ((∫ s in Ioc (0 : ℝ) u, (g s.toNNReal).re : ℝ) : ℂ) +
        ((∫ s in Ioc (0 : ℝ) u, (g s.toNNReal).im : ℝ) : ℂ) * Complex.I := by
    funext u
    have hr := Complex.reCLM.integral_comp_comm (hg u)
    have hi := Complex.imCLM.integral_comp_comm (hg u)
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
    rw [hr, hi]
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **The compensated process is driftless.** -/
theorem isNativeItoProcess_sub_drift {F b : ℝ≥0 → DriverSample S κ → ℂ}
    {φ : κ → ℝ≥0 → DriverSample S κ → ℂ} (hF : IsNativeItoProcess μ F b φ) :
    IsNativeItoProcess μ (fun t x => F t x - F 0 x - ∫ s in Ioc (0 : ℝ) t, b s.toNNReal x)
      (fun _ _ => 0) φ := by
  have hI := ModelExist.isStronglyProgressive_integral_C hF.drift_progressive
  have h0 : IsStronglyProgressive (driverAugmented (κ := κ) μ) (fun (_ : ℝ≥0) x => F 0 x) :=
    fun i => ((hF.adapted 0).mono ((driverAugmented (κ := κ) μ).mono zero_le)).comp_measurable
      measurable_snd
  have hp := (hF.progressive.sub h0).sub hI
  refine ⟨fun t => hp.stronglyAdapted t, hp, ?_, fun _ => stronglyMeasurable_const,
    hF.diffusion_progressive, ae_of_all _ fun _ _ => integrableOn_zero, hF.localizing, ?_⟩
  · filter_upwards [hF.continuous, hF.drift_integrable] with x hx hb
    exact (hx.sub continuous_const).sub (continuous_setIntegral_Ioc_C' (g := fun u => b u x) hb)
  · intro ℓ τ hτ T hG t ht
    obtain ⟨hs, hid⟩ := hF.identity ℓ τ hτ T hG t ht
    refine ⟨hs, ?_⟩
    filter_upwards [hid, hF.drift_integrable] with x h1 h2
    rw [← h1]
    have hd : stoppedDrift τ b t x = ∫ v in Ioc (0 : ℝ) (stopTime (τ x) t), b v.toNNReal x :=
      setIntegral_switch (fun v => b v.toNNReal x) (τ x) t
    have hz : stoppedDrift τ (fun (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : ℂ)) t x = 0 := by
      simp only [stoppedDrift, ite_self, integral_zero]
    simp only [stoppedProcess_eq_stopTime, hd, hz, map_sub, map_zero, NNReal.coe_zero,
      Ioc_self, Measure.restrict_empty, integral_zero_measure, sub_self, sub_zero]

end BlockBand.SourceProcess.ComplexCoupled
