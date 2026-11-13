module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFullProcess

/-!
# Existence of the continuous Itô integral process

`nativeContinuousIntegral_exists`: every predictable `L²` family has a continuous adapted
square-integrable martingale integral process whose value at the horizon is the Itô integral
`fullNativeIntegral`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- The `L²` class of the limit process at the horizon is the Itô integral. -/
theorem nativeAdaptedLimit_terminal_toLp
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    (nativeAdaptedLimit_memLp_all μ T f T).toLp (nativeAdaptedLimit μ T f T) =
      fullNativeIntegral (κ := κ) μ T f := by
  exact (MemLp.toLp_congr (nativeAdaptedLimit_memLp_all μ T f T)
    (Lp.memLp (fullNativeIntegral (κ := κ) μ T f))
    (nativeAdaptedLimit_terminal_ae μ T f)).trans (Lp.toLp_coeFn _ _)

/-- Before the horizon, the `L²` class of the limit process is the timewise projection. -/
theorem nativeAdaptedLimit_toLp_projection
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : u ≤ T) :
    (nativeAdaptedLimit_memLp_all μ T f u).toLp (nativeAdaptedLimit μ T f u) =
      nativeTimewiseProjection μ T f u := by
  exact (MemLp.toLp_congr (nativeAdaptedLimit_memLp_all μ T f u)
    (Lp.memLp (nativeTimewiseProjection μ T f u))
    (nativeAdaptedLimit_ae_projection μ T f hu)).trans (Lp.toLp_coeFn _ _)

/-- The `L²` norm of the limit process at any time is at most the norm of the predictable family. -/
theorem nativeAdaptedLimit_L2_norm_le
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    ‖(nativeAdaptedLimit_memLp_all μ T f u).toLp (nativeAdaptedLimit μ T f u)‖ ≤ ‖f‖ := by
  by_cases hu : u ≤ T
  · rw [nativeAdaptedLimit_toLp_projection μ T f hu]
    exact nativeTimewiseProjection_norm μ T f u
  · have he := nativeAdaptedLimit_after_horizon μ T f (le_of_not_ge hu)
    have hc : (nativeAdaptedLimit_memLp_all μ T f u).toLp (nativeAdaptedLimit μ T f u) =
        (nativeAdaptedLimit_memLp_all μ T f T).toLp (nativeAdaptedLimit μ T f T) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun he))
    rw [hc, nativeAdaptedLimit_terminal_toLp]
    exact (fullNativeIntegral_norm μ T f).le

/-- **The continuous Itô integral process.** For every predictable family on `(0,T]`, under `dt`
times `μ` times independent Wiener paths, there is an adapted martingale, square integrable at every
time, with almost surely continuous paths, whose value at `T` is the Itô integral. -/
theorem nativeContinuousIntegral_exists
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ∃ X : ℝ≥0 → DriverSample S κ → ℝ,
      (∀ u, Measurable[commonWienerFiltration S κ u] (X u)) ∧
      Martingale X (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) ∧
      (∀ u, MemLp (X u) 2 (driverLaw (κ := κ) μ)) ∧
      (∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous (fun u => X u x)) ∧
      (X T =ᵐ[driverLaw (κ := κ) μ]
        (fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ)) := by
  exact ⟨nativeAdaptedLimit μ T f, nativeAdaptedLimit_adapted μ T f,
    nativeAdaptedLimit_martingale μ T f, nativeAdaptedLimit_memLp_all μ T f,
    nativeAdaptedLimit_continuous_all_ae μ T f, nativeAdaptedLimit_terminal_ae μ T f⟩

end BlockBand.SourceProcess.FiniteDriverCompletion
