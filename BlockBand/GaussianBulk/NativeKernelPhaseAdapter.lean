module
public import BlockBand.GaussianBulk.PhaseProductAdapter

/-!
# The Johansson integrand in terms of the saddle phase

The integrand of Johansson's double contour kernel, at time `S = t/N` and microscopic points
`u = E + ξ/(Nρ)`, `v = E + ζ/(Nρ)`, is the exponential of `N` times the saddle phase difference
plus linear microscopic terms, divided by `w - z`; after the real microscopic gauge it is
`gaugedJohanssonExp / (w - z)`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open scoped NNReal

/-- The Johansson integrand at `S = t/N` equals the exponential of `N` times the phase
difference plus the microscopic linear corrections, divided by `w - z`. -/
theorem nativeKernelIntegrand_eq_phase {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E rho xi zeta : ℝ) (t : ℝ≥0) (ht : 0 < t) (hrho : 0 < rho) (z w : ℂ)
    (hz : ∀ j,z-(d j:ℂ)≠0) (hw : ∀ j,w-(d j:ℂ)≠0) :
    BlockBand.External.Johansson.kernelIntegrand
      (BlockBand.External.Johansson.sourceTime N t) d
      (E+xi/((N:ℝ)*rho)) (E+zeta/((N:ℝ)*rho)) z w =
      Complex.exp ((N:ℂ)*(saddlePhase d E (t:ℝ) w-saddlePhase d E (t:ℝ) z)+
        (((xi/((t:ℝ)*rho):ℝ):ℂ)*z-((zeta/((t:ℝ)*rho):ℝ):ℂ)*w))/(w-z) := by
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have htR : 0 < (t:ℝ) := ht
  have htc : ((t:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htR)
  have hrc : (rho:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hrho)
  have hs : (BlockBand.External.Johansson.sourceTime N t:ℂ)=((t:ℝ):ℂ)/(N:ℂ) := by
    rw [BlockBand.External.Johansson.sourceTime_coe,Complex.ofReal_div,Complex.ofReal_natCast]
  have he : (w^2-2*((E+zeta/((N:ℝ)*rho):ℝ):ℂ)*w-z^2+
      2*((E+xi/((N:ℝ)*rho):ℝ):ℂ)*z)/
        (2*(BlockBand.External.Johansson.sourceTime N t:ℂ)) =
      (N:ℂ)*(((w-(E:ℂ))^2-(z-(E:ℂ))^2)/(2*((t:ℝ):ℂ)))+
        (((xi/((t:ℝ)*rho):ℝ):ℂ)*z-((zeta/((t:ℝ)*rho):ℝ):ℂ)*w) := by
    rw [hs]
    push_cast
    field_simp [hn,htc,hrc]
    ring
  unfold BlockBand.External.Johansson.kernelIntegrand
  rw [he]
  simp only [Complex.exp_add]
  rw [exp_saddlePhase_difference_product hN d E (t:ℝ) z w hz hw]
  ring

/-- After the real microscopic prefactor and gauge, the Johansson integrand is
`gaugedJohanssonExp / (w - z)`. -/
theorem gaugedNativeKernelIntegrand_eq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E rho x₀ xi zeta : ℝ) (t : ℝ≥0) (ht : 0 < t) (hrho : 0 < rho) (z w : ℂ)
    (hz : ∀ j,z-(d j:ℂ)≠0) (hw : ∀ j,w-(d j:ℂ)≠0) :
    let beta : ℝ := (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*(t:ℝ))
    Complex.exp (((beta-realSineGauge N E (t:ℝ) rho x₀ xi+
        realSineGauge N E (t:ℝ) rho x₀ zeta:ℝ):ℂ))*
      BlockBand.External.Johansson.kernelIntegrand
        (BlockBand.External.Johansson.sourceTime N t) d
        (E+xi/((N:ℝ)*rho)) (E+zeta/((N:ℝ)*rho)) z w =
      gaugedJohanssonExp d E (t:ℝ) rho x₀ xi zeta z w/(w-z) := by
  rw [nativeKernelIntegrand_eq_phase hN d E rho xi zeta t ht hrho z w hz hw]
  unfold gaugedJohanssonExp
  simp only [Complex.exp_add,Complex.exp_sub]
  ring

end BlockBand.GaussianBulk
