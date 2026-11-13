module
public import BlockBand.SourceProcess.Stochastic.Integral.Limit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The continuous stopped stochastic integral

`continuousStoppedIntegral_holds` proves the statement `ContinuousStoppedIntegral μ`
of `BlockBand.SourceProcess.Stochastic.Basic` for every measurable old-state space `S`,
finite noise index `κ` and probability `μ`. Measure `driverLaw μ`, raw filtration
`commonWienerFiltration S κ`, stopping times for the augmented filtration `F_t ∨ N`, integrands
in `L²(dt ⊗ driverLaw μ)` on `(0,T]` with a raw-predictable representative.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion

/-- **`ContinuousStoppedIntegral`**: continuous stochastic integral identified with the
terminal integral of every stopped integrand. -/
theorem continuousStoppedIntegral_holds {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] : ContinuousStoppedIntegral (κ := κ) μ := by
  classical
  intro T g hg
  refine ⟨nativeAdaptedLimit μ T hg.family, nativeAdaptedLimit_adapted μ T _,
    nativeAdaptedLimit_martingale μ T _, nativeAdaptedLimit_memLp_all μ T _,
    fun x => congrFun (nativeAdaptedLimit_initial μ T _) x,
    nativeAdaptedLimit_continuous_all_ae μ T _, ?_⟩
  intro τ hτ u
  have hne (x : DriverSample S κ) : min (u : WithTop ℝ≥0) (τ x) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  let σ : DriverSample S κ → ℝ≥0 := fun x => (min (u : WithTop ℝ≥0) (τ x)).untop (hne x)
  have hσcoe (x : DriverSample S κ) : (σ x : WithTop ℝ≥0) = min (u : WithTop ℝ≥0) (τ x) :=
    WithTop.coe_untop _ _
  have hσu (x : DriverSample S κ) : σ x ≤ u := by
    have h := min_le_left (u : WithTop ℝ≥0) (τ x)
    rw [← hσcoe x] at h
    exact_mod_cast h
  have hσ (t : ℝ≥0) : MeasurableSet[driverAugmented (κ := κ) μ t] {x | σ x ≤ t} := by
    have he : {x | σ x ≤ t} = {ω | min (τ ω) (u : WithTop ℝ≥0) ≤ t} := by
      ext x
      change σ x ≤ t ↔ min (τ x) (u : WithTop ℝ≥0) ≤ t
      rw [min_comm, ← hσcoe x, WithTop.coe_le_coe]
    rw [he]
    exact hτ.min_const u t
  have hst : stopIntegrand (fun x => min (u : WithTop ℝ≥0) (τ x)) g = stopFn σ g := by
    rw [← stopIntegrand_coe]
    congr 1
    funext x
    exact (hσcoe x).symm
  rw [hst]
  obtain ⟨hs, hae⟩ := stopped_identity_of_bounded hg hσu hσ
  refine ⟨hs, ?_⟩
  have hsp : stoppedProcess (nativeAdaptedLimit μ T hg.family) τ u =
      fun x => nativeAdaptedLimit μ T hg.family (σ x) x := by
    funext x
    simp only [stoppedProcess]
    rw [WithTop.untopA_eq_untop (hne x)]
  rw [hsp]
  exact hae

end BlockBand.SourceProcess.Stochastic.Integral
